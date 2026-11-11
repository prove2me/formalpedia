-- Prove2me | Definitions.Def_MCAListDecoding_PowersGenerator_Curves
-- name    : MCAListDecoding_PowersGenerator_Curves
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:04.233231+00:00
-- url     : https://prove2.me/theorems/aa43ccb5-aed2-409a-9a38-6ca6f2bb555a
-- title:
--   Decoded codewords, full agreement sets, curves and coherent tuples
-- statement:
--   Fix a code $C\subseteq\Sigma^n$, $d\ge1$, words $u_0,\dots,u_d$ and an integer radius $e=\gamma n$.
--
--   * The **decoded codeword** $c_x$ of a seed $x$: a codeword within Hamming distance $e$ of $u(x)$ (Lemma 4.2; unique on bad seeds when $2e<\Delta_C$).
--   * The **full agreement set** $A(x)=\{i\in[n] : u_i(x)=c_x[i]\}$.
--   * A **curve** (codeword polynomial) $P(X)=\sum_{j=0}^d P_jX^j$ with every $P_j\in C$; its evaluation $P(x)=\sum_j x^jP_j$.
--   * Its **domain** $T_P=\{i : u_i(X)\equiv P_i(X)\}=\{i : u_j[i]=P_j[i]\ \forall j\}$ (coefficientwise), $z_P=|T_P|/n$ and $s_P=n-|T_P|$. A seed $x$ lies on $P$ if $c_x=P(x)$.
--   * A tuple $(x_1,\dots,x_{d+2})$ of seeds is **coherent** if all decoded points $(x_m,c_{x_m})$ lie on one curve.
--   * The **common agreement set** $A(x_1)\cap\dots\cap A(x_k)$ of a tuple.
--
--   **Formalization Note.** `decoded C d e u x` picks such a codeword with `Classical.choose` when one exists and is $0$ otherwise; only its values on bad seeds under $2e<\Delta_C$ are used, where it is the paper's unique $c_x$. Distinctness and badness of a tuple's seeds are hypotheses of the lemmas, not part of `IsCoherent`.
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.2 p. 27 (c_x, A(x)), Definition 4.4 and Definition 4.7 p. 28

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code

/-!
# Decoded codewords, full agreement sets, curves and coherent tuples

Manzur, *Mutual Correlated Agreement and List-Decoding: Improvements and Separations*,
STOC 2027 submission (manuscript of 2026-11-03), §4: Lemma 4.2 (p. 27), Definitions 4.4 and 4.7
(p. 28).

The radius is an integer `e = γ n ∈ {0, …, n}` (the paper's convention (2), p. 27), so the
real radius used in `badSeeds` is `γ = e / n`.

**Formalization Note.** `decoded C d e u x` is a codeword of `C` within distance `e` of the
combined word `u(x)` when one exists (chosen with `Classical.choose`), and `0` otherwise. Under
`2e < Δ_C` such a codeword is unique for every bad seed (Lemma 4.2), so on bad seeds it is the
paper's `c_x`; its value on other seeds is never used.
-/

namespace MCAListDecoding.PowersGenerator

variable {F Alph : Type*} [Field F] [AddCommGroup Alph] [Module F Alph] {n : ℕ}

/-- The agreement set `{i : w[i] = c[i]}` of two words. -/
noncomputable def agreeSet (w c : Fin n → Alph) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => w i = c i

/-- The decoded codeword `c_x` (Lemma 4.2, p. 27): a codeword within Hamming distance `e` of
`u(x)` if one exists, `0` otherwise. -/
noncomputable def decoded (C : Submodule F (Fin n → Alph)) (d e : ℕ)
    (u : Fin (d + 1) → Fin n → Alph) (x : F) : Fin n → Alph := by
  classical
  exact if h : ∃ c ∈ C, hamDist (combinedWord d u x) c ≤ e then h.choose else 0

/-- The full agreement set `A(x) = {i ∈ [n] : u_i(x) = c_x[i]}` (Lemma 4.2, p. 27). -/
noncomputable def agreementSet (C : Submodule F (Fin n → Alph)) (d e : ℕ)
    (u : Fin (d + 1) → Fin n → Alph) (x : F) : Finset (Fin n) :=
  agreeSet (combinedWord d u x) (decoded C d e u x)

/-- A codeword polynomial, or **curve**, `P(X) = ∑_{j=0}^{d} P_j X^j` with every `P_j ∈ C`
(Definition 4.4, p. 28), given by its coefficient tuple. -/
abbrev Curve (C : Submodule F (Fin n → Alph)) (d : ℕ) := Fin (d + 1) → C

/-- Evaluation `P(x) = ∑_j x^j P_j` of a curve at `x ∈ F`. -/
def curveEval {C : Submodule F (Fin n → Alph)} {d : ℕ} (P : Curve C d) (x : F) : Fin n → Alph :=
  ∑ j : Fin (d + 1), x ^ (j : ℕ) • ((P j : C) : Fin n → Alph)

/-- The domain `T_P = {i ∈ [n] : u_i(X) ≡ P_i(X)}` of a curve: the coordinates where the two
polynomials agree coefficientwise, i.e. `u_j[i] = P_j[i]` for every `j` (Definition 4.4). -/
noncomputable def curveDomain {C : Submodule F (Fin n → Alph)} {d : ℕ}
    (u : Fin (d + 1) → Fin n → Alph) (P : Curve C d) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∀ j : Fin (d + 1), u j i = ((P j : C) : Fin n → Alph) i

/-- `z_P = |T_P| / n` (Definition 4.4). -/
noncomputable def curveZ {C : Submodule F (Fin n → Alph)} {d : ℕ}
    (u : Fin (d + 1) → Fin n → Alph) (P : Curve C d) : ℝ :=
  ((curveDomain u P).card : ℝ) / n

/-- `s_P = n - |T_P|` (Definition 4.4); `|T_P| ≤ n`, so the natural subtraction is exact. -/
noncomputable def curveS {C : Submodule F (Fin n → Alph)} {d : ℕ}
    (u : Fin (d + 1) → Fin n → Alph) (P : Curve C d) : ℕ :=
  n - (curveDomain u P).card

/-- A tuple of `h = d + 2` seeds is **coherent** if all its decoded points `(x_m, c_{x_m})` lie on
a single curve: `c_{x_m} = P(x_m)` for every `m` (Definition 4.7, p. 28). Distinctness and
badness of the seeds are hypotheses of the statements that use it. -/
def IsCoherent (C : Submodule F (Fin n → Alph)) (d e : ℕ) (u : Fin (d + 1) → Fin n → Alph)
    (xs : Fin (d + 2) → F) : Prop :=
  ∃ P : Curve C d, ∀ m : Fin (d + 2), decoded C d e u (xs m) = curveEval P (xs m)

/-- The common agreement set `A(x_1) ∩ ⋯ ∩ A(x_k)` of a tuple of seeds. -/
noncomputable def commonAgreement (C : Submodule F (Fin n → Alph)) (d e : ℕ)
    (u : Fin (d + 1) → Fin n → Alph) {k : ℕ} (xs : Fin k → F) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∀ m : Fin k, i ∈ agreementSet C d e u (xs m)

end MCAListDecoding.PowersGenerator


