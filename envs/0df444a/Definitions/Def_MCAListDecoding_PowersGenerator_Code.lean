-- Prove2me | Definitions.Def_MCAListDecoding_PowersGenerator_Code
-- name    : MCAListDecoding_PowersGenerator_Code
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:17:24.316351+00:00
-- url     : https://prove2.me/theorems/bff8bad8-be32-4a78-a2d8-07e9660fb9e2
-- title:
--   Linear codes over a vector-space alphabet, minimum distance, the powers generator and MCA-bad seeds
-- statement:
--   Let $F$ be a field and $\Sigma$ (in Lean `Alph`) an $F$-vector space. Words of length $n$ are maps $[n]\to\Sigma$ (Lean: `Fin n → Alph`, coordinates $0,\dots,n-1$). An **$F$-linear code** is an $F$-subspace $C\subseteq\Sigma^n$.
--
--   * The **Hamming distance** $\Delta(u,v)=|\{i : u[i]\ne v[i]\}|$ and **weight** $\mathrm{wt}(v)=\Delta(v,0)$.
--   * The **minimum distance** $\Delta_C$ is the minimum weight of a nonzero codeword (for a nonzero linear code, the minimum distance between distinct codewords), and $\delta_C=\Delta_C/n$.
--   * **Restricted membership** $w|_T\in C|_T$ for $T\subseteq[n]$: some codeword agrees with $w$ on every coordinate of $T$.
--   * The **univariate powers generator** $G_d(x)=(1,x,\dots,x^d)$ combines words $u_0,\dots,u_d$ into $u(x)=\sum_{j=0}^d x^j u_j$.
--   * A seed $x$ is **MCA-bad** for $u_0,\dots,u_d$ and the radius $\gamma$ if there is $T\subseteq[n]$ with $|T|\ge n(1-\gamma)$, $u(x)|_T\in C|_T$, and $u_j|_T\notin C|_T$ for some $j\in\{0,\dots,d\}$ (the same $T$ in both clauses). $B=B_C(U;\gamma)$ is the set of MCA-bad seeds in the seed set $S\subseteq F$.
--   * The **generalized Johnson radius** $J_h(\delta)=1-(1-\delta)^{1/h}$ (a real power).
--   * The integer-radius convention: a real $\gamma$ is replaced by $\lfloor \gamma n\rfloor/n$ (`roundRadius n γ`).
--
--   **Formalization Note.** `minDist C` is `sInf` of the weights of nonzero codewords; it is $0$ for $C=\bot$, where the paper's $\Delta_C$ is undefined, and every statement of this mission using it assumes $C\ne\bot$. Real division by $n=0$ gives $0$, but $C\ne\bot$ forces $n\ge 1$.
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), §3.1 p. 24 (Hamming distance, Δ_C, C|_T), p. 25 (J_h, Definition 3.3, Definition 3.4), p. 27 (Definition 4.1, convention (2))

import Mathlib

/-!
# Linear codes over a vector-space alphabet, the powers generator and MCA-bad seeds

Manzur, *Mutual Correlated Agreement and List-Decoding: Improvements and Separations*,
STOC 2027 submission (manuscript of 2026-11-03), §3.1–3.2 (pp. 24–25) and Definition 4.1 (p. 27).

* `F` is a field, `Alph` (the paper's `Σ`) an `F`-vector space; words are `Fin n → Alph`
  (coordinates `0, …, n-1` for the paper's `[n] = {1, …, n}`).
* An `F`-linear code is a `Submodule F (Fin n → Alph)`.
* The words `u_0, …, u_d` are a tuple `u : Fin (d + 1) → (Fin n → Alph)`.

**Formalization Note.** `minDist C` is the minimum weight of a nonzero codeword (the paper's `Δ_C`
for a nonzero linear code). For `C = ⊥` the set of weights is empty and `sInf ∅ = 0`; the paper's
`Δ_C` is undefined there, and every statement of this mission that uses it assumes `C ≠ ⊥`.
-/

namespace MCAListDecoding.PowersGenerator

variable {F Alph : Type*} [Field F] [AddCommGroup Alph] [Module F Alph] {n : ℕ}

/-- Hamming distance `Δ(u, v) = |{i : u[i] ≠ v[i]}|` between two words over the alphabet `Alph`. -/
noncomputable def hamDist (u v : Fin n → Alph) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => u i ≠ v i).card

/-- Hamming weight `wt(v) = |{i : v[i] ≠ 0}|`. -/
noncomputable def hamWeight (v : Fin n → Alph) : ℕ := hamDist v 0

/-- Minimum distance `Δ_C` of an `F`-linear code: the minimum weight of a nonzero codeword
(equal to the minimum distance between distinct codewords, p. 24). `0` for `C = ⊥` (undefined in
the paper; excluded by hypothesis wherever used). -/
noncomputable def minDist (C : Submodule F (Fin n → Alph)) : ℕ :=
  sInf {w : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hamWeight c = w}

/-- Relative distance `δ_C = Δ_C / n`. -/
noncomputable def relDist (C : Submodule F (Fin n → Alph)) : ℝ :=
  (minDist C : ℝ) / n

/-- Restricted-code membership `w|_T ∈ C|_T`: some codeword agrees with `w` on every coordinate
of `T` (p. 24). This is not a distance condition. -/
def RestrictMem (C : Submodule F (Fin n → Alph)) (T : Finset (Fin n)) (w : Fin n → Alph) : Prop :=
  ∃ c ∈ C, ∀ i ∈ T, c i = w i

/-- The combined word of the univariate powers generator `G_d(x) = (1, x, …, x^d)` at the seed
`x`: `u(x) = ∑_{j=0}^{d} x^j u_j` (Definition 3.3, p. 25). -/
def combinedWord (d : ℕ) (u : Fin (d + 1) → Fin n → Alph) (x : F) : Fin n → Alph :=
  ∑ j : Fin (d + 1), x ^ (j : ℕ) • u j

/-- A seed `x` is **MCA-bad** for the words `u` and the real radius `γ` (Definition 3.4, p. 25,
and Definition 4.1, p. 27) if there is `T ⊆ [n]` with `|T| ≥ n(1 - γ)` such that the combined
word restricted to `T` lies in `C|_T` while some `u_j` restricted to the *same* `T` does not. -/
def IsMCABad (C : Submodule F (Fin n → Alph)) (d : ℕ) (γ : ℝ) (u : Fin (d + 1) → Fin n → Alph)
    (x : F) : Prop :=
  ∃ T : Finset (Fin n), (n : ℝ) * (1 - γ) ≤ (T.card : ℝ) ∧
    RestrictMem C T (combinedWord d u x) ∧ ∃ j : Fin (d + 1), ¬ RestrictMem C T (u j)

/-- The set `B = B_C(U; γ) ⊆ S` of MCA-bad seeds in the seed set `S` (Definition 4.1, p. 27). -/
noncomputable def badSeeds (C : Submodule F (Fin n → Alph)) (d : ℕ) (γ : ℝ)
    (u : Fin (d + 1) → Fin n → Alph) (S : Finset F) : Finset F := by
  classical
  exact S.filter fun x => IsMCABad C d γ u x

/-- Generalized Johnson radius `J_h(δ) = 1 - (1 - δ)^{1/h}` (p. 25), a real power. -/
noncomputable def johnsonRadius (h : ℕ) (δ : ℝ) : ℝ :=
  1 - (1 - δ) ^ ((1 : ℝ) / (h : ℝ))

/-- The integer-radius convention (display (2), p. 27): a real radius `γ` is replaced by
`⌊γ n⌋ / n` in hypotheses and bounds. -/
noncomputable def roundRadius (n : ℕ) (γ : ℝ) : ℝ :=
  (Nat.floor (γ * n) : ℝ) / n

end MCAListDecoding.PowersGenerator


