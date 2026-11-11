-- Prove2me | Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction
-- name    : QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:38.325019+00:00
-- url     : https://prove2.me/theorems/6bba2ff2-8ef6-4b15-91df-81e64ef0d223
-- title:
--   §4.1 — the group $G$, the operators $P_{\pm i}$, the map $S(\cdot)$, the iterates $V_n$ and the weighted norm
-- statement:
--   Fix a number $s$ of generators and let
--   $$
--   G=\langle g_1,\dots,g_s\mid g_i^2=e\text{ for all } i\in[s]\rangle
--   $$
--   be the free product of $s$ copies of $\mathbb Z/2$. Its elements are reduced words in the letters $1,\dots,s$ with no two equal adjacent letters; $|g|$ is the length of the reduced word and $e$ the empty word.
--
--   On $H=\ell^2(G)$ with basis $\{|g\rangle\}_{g\in G}$ let $L_g|w\rangle=|gw\rangle$ and $R_g|w\rangle=|wg\rangle$. For each letter $i$ the source defines the orthogonal projections
--   $$
--   P_{+i}=\tfrac14(I+L_i)(I+R_i),\qquad P_{-i}=\tfrac14(I-L_i)(I-R_i),
--   $$
--   the operator $E=|e\rangle\langle e|$, the map
--   $$
--   S(X)=\sum_{i=1}^s\bigl(P_{+i}XP_{-i}+P_{-i}XP_{+i}\bigr),
--   $$
--   and the iterates (eq. (2))
--   $$
--   V_0=0,\qquad V_{n+1}=V_n+\tfrac2s\bigl(E-S(V_n)\bigr).
--   $$
--   An operator $X$ is recorded by its coefficients $X(g,h)=\langle g|X|h\rangle$. The Frobenius norm is $\|X\|_F=(\sum_{g,h}|X(g,h)|^2)^{1/2}$, and the weighted norm of Proposition 4.4 is
--   $$
--   \|X\|_w=\sum_{k,\ell\ge0}2^{(k+\ell)/2}\|X_{k,\ell}\|_F,\qquad X_{k,\ell}=\sum_{|g|=k,\ |h|=\ell}X(g,h)|g\rangle\langle h|.
--   $$
--   $X$ lies in $\mathcal S=\operatorname{span}\{|g\rangle\langle h|:g,h\in G\}$ when it has finitely many nonzero coefficients. The module also fixes the contraction constant $\lambda=3/4+24/\sqrt{2s}$ of Lemma 4.5.
--
--   These are the objects of the infinite-dimensional construction of §4.1: $V_n$ converges to an operator $V$ with $S(V)=E$, from which the 1-dependent colouring is built.
--
--   **Formalization Note** $G$ is the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries $0$, which Mathlib reads as $\infty$), and $|g|$ its Coxeter length; generators are indexed by `Fin s` instead of $[s]$. An operator is its coefficient array `G s × G s → ℂ`; since $L_i$, $R_i$ permute the basis, $L_iX$, $R_iX$, $XL_i$, $XR_i$ are reindexings ($(L_iX)(g,h)=X(g_i^{-1}g,h)$, $(XL_i)(g,h)=X(g,g_ih)$, and similarly for $R_i$), and $P_{\pm i}X$, $XP_{\pm i}$ are their expansions. $S(\cdot)$ is built literally from the $P_{\pm i}$. Both norms take values in $[0,\infty]$, so they are meaningful for every coefficient array.
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, §3 p.10 (Frobenius norm), §4.1 pp.13–14 (G, L_g, R_g, P_{±i}, eq. (2)), §2.1 p.6 (E), Proposition 4.4 p.14 (weighted norm), Lemma 4.5 p.14 (λ) — PDF pp.13, 16–17, 9

import Mathlib

open scoped ENNReal

/-!
# The infinite-dimensional construction: the group `G`, the operators `P_{±i}`, `S(·)` and `V_n`

Maxime Flin, Longcheng Li, Jukka Suomela, *Quantum Advantage for Distributed Symmetry Breaking*,
STOC 2027 submission #863 (October 2026), §3 p.10 (Frobenius norm), §4.1 pp.13–14 (the group `G`,
the operators `L_g`, `R_g`, `P_{±i}`, `E`, the map `S(·)` and the recursion (2)), Proposition 4.4
p.14 (the weighted norm).

`G = ⟨g_1, …, g_s | g_i² = e⟩` is the free product of `s` copies of `ℤ/2`, encoded as the universal
Coxeter group on `Fin s` (Mathlib's Coxeter matrix with every off-diagonal entry `0`, which in
Mathlib's convention means "no relation", i.e. `m = ∞`). The generator `g_i` is `gen s i` and `|g|`
is the Coxeter length (the reduced-word length).

An operator `X` on `H = ℓ²(G)` is recorded by its matrix coefficients `X(g, h) = ⟨g|X|h⟩`, a function
`G × G → ℂ` (`Op s`). The operators `L_i`, `R_i` permute the basis, so left and right multiplication of
`X` by them is a reindexing of the coefficients; `P_{±i} X` and `X P_{±i}` are obtained by expanding
`P_{±i} = (I ± L_i)(I ± R_i)/4`. The span `S = span{|g⟩⟨h|}` is the set of `X` with finitely many nonzero
coefficients. Norms of coefficient arrays are taken in `ℝ≥0∞`, so that they are meaningful (possibly
`∞`) for every `X`, not only for `X ∈ S`.
-/

namespace QuantumSymmetryBreaking.CycleColoring

/-- The Coxeter matrix of the universal Coxeter group on `s` generators: `1` on the diagonal,
`0` (Mathlib's encoding of `∞`, no relation) off the diagonal. -/
def coxMat (s : ℕ) : CoxeterMatrix (Fin s) where
  M := fun i j => if i = j then 1 else 0
  isSymm := Matrix.IsSymm.ext fun i j => by
    by_cases h : i = j
    · subst h; rfl
    · simp only [if_neg h, if_neg (Ne.symm h)]
  diagonal := by intro i; simp
  off_diagonal := by intro i j h; simp [h]

/-- §4.1, p.13: the group `G = ⟨g_1, …, g_s | g_i² = e for all i ∈ [s]⟩`, the free product of `s`
copies of `ℤ/2` (the universal Coxeter group on `Fin s`). -/
abbrev G (s : ℕ) : Type := (coxMat s).Group

/-- The generator `g_i` of `G` (written `i` in the source). The source indexes generators by
`[s] = {1, …, s}`; here by `Fin s = {0, …, s-1}`. -/
noncomputable def gen (s : ℕ) (i : Fin s) : G s := (coxMat s).simple i

/-- `|g|`, the length of a reduced word for `g ∈ G` (the Coxeter length). -/
noncomputable def len {s : ℕ} (g : G s) : ℕ := (coxMat s).toCoxeterSystem.length g

/-- An operator on `H = ℓ²(G)` recorded by its coefficients `X(g, h) = ⟨g|X|h⟩`. -/
abbrev Op (s : ℕ) : Type := G s × G s → ℂ

/-- The coefficients of `L_i X`, where `L_g|w⟩ = |gw⟩`: `(L_i X)(g, h) = X(g_i⁻¹ g, h)`
(`= X(g_i g, h)` since `g_i` is an involution). -/
noncomputable def mulLleft {s : ℕ} (i : Fin s) (X : Op s) : Op s := fun p => X ((gen s i)⁻¹ * p.1, p.2)

/-- The coefficients of `R_i X`, where `R_g|w⟩ = |wg⟩`: `(R_i X)(g, h) = X(g g_i⁻¹, h)`. -/
noncomputable def mulRleft {s : ℕ} (i : Fin s) (X : Op s) : Op s := fun p => X (p.1 * (gen s i)⁻¹, p.2)

/-- The coefficients of `X L_i`: `(X L_i)(g, h) = ⟨g|X L_i|h⟩ = X(g, g_i h)`. -/
noncomputable def mulLright {s : ℕ} (i : Fin s) (X : Op s) : Op s := fun p => X (p.1, gen s i * p.2)

/-- The coefficients of `X R_i`: `(X R_i)(g, h) = ⟨g|X R_i|h⟩ = X(g, h g_i)`. -/
noncomputable def mulRright {s : ℕ} (i : Fin s) (X : Op s) : Op s := fun p => X (p.1, p.2 * gen s i)

/-- §4.1, p.13: `P_{+i} X` with `P_{+i} = (I + L_i)(I + R_i)/4`, i.e.
`(X + R_i X + L_i X + L_i R_i X)/4`. -/
noncomputable def projPlusLeft {s : ℕ} (i : Fin s) (X : Op s) : Op s :=
  (1 / 4 : ℂ) • (X + mulRleft i X + mulLleft i X + mulLleft i (mulRleft i X))

/-- §4.1, p.13: `P_{-i} X` with `P_{-i} = (I - L_i)(I - R_i)/4`, i.e.
`(X - R_i X - L_i X + L_i R_i X)/4`. -/
noncomputable def projMinusLeft {s : ℕ} (i : Fin s) (X : Op s) : Op s :=
  (1 / 4 : ℂ) • (X - mulRleft i X - mulLleft i X + mulLleft i (mulRleft i X))

/-- `X P_{+i} = X (I + L_i)(I + R_i)/4 = (X + X L_i + X R_i + X L_i R_i)/4`. -/
noncomputable def projPlusRight {s : ℕ} (i : Fin s) (X : Op s) : Op s :=
  (1 / 4 : ℂ) • (X + mulLright i X + mulRright i X + mulRright i (mulLright i X))

/-- `X P_{-i} = X (I - L_i)(I - R_i)/4 = (X - X L_i - X R_i + X L_i R_i)/4`. -/
noncomputable def projMinusRight {s : ℕ} (i : Fin s) (X : Op s) : Op s :=
  (1 / 4 : ℂ) • (X - mulLright i X - mulRright i X + mulRright i (mulLright i X))

open Classical in
/-- §2.1 p.6 and §4.1: the operator `E = |e⟩⟨e|`. -/
noncomputable def opE (s : ℕ) : Op s := fun p => if p = (1, 1) then 1 else 0

/-- Eq. (2), p.13: `S(X) = ∑_{i=1}^s (P_{+i} X P_{-i} + P_{-i} X P_{+i})`. -/
noncomputable def opS {s : ℕ} (X : Op s) : Op s :=
  ∑ i : Fin s, (projPlusLeft i (projMinusRight i X) + projMinusLeft i (projPlusRight i X))

/-- Eq. (2), p.13: `V_0 = 0`, `V_{n+1} = V_n + (2/s)(E - S(V_n))`. -/
noncomputable def opV (s : ℕ) : ℕ → Op s
  | 0 => 0
  | n + 1 => opV s n + ((2 : ℂ) / s) • (opE s - opS (opV s n))

/-- §3, p.10: the Frobenius norm `‖X‖_F = (∑_{g,h} |X(g,h)|²)^{1/2}`, in `ℝ≥0∞` (it is `∞` exactly
when `X` is not Hilbert–Schmidt). -/
noncomputable def opFrob {s : ℕ} (X : Op s) : ℝ≥0∞ :=
  (∑' p : G s × G s, (‖X p‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)

open Classical in
/-- Proposition 4.4, p.14: the block `X_{k,ℓ} = ∑_{|g| = k, |h| = ℓ} X(g,h) |g⟩⟨h|`. -/
noncomputable def opBlock {s : ℕ} (X : Op s) (k l : ℕ) : Op s := fun p =>
  if len p.1 = k ∧ len p.2 = l then X p else 0

/-- Proposition 4.4, p.14: the weighted norm `‖X‖_w = ∑_{k,ℓ ≥ 0} 2^{(k+ℓ)/2} ‖X_{k,ℓ}‖_F`
(in `ℝ≥0∞`; for `X ∈ S` it is the finite sum of the source). -/
noncomputable def opW {s : ℕ} (X : Op s) : ℝ≥0∞ :=
  ∑' kl : ℕ × ℕ, ENNReal.ofReal ((2 : ℝ) ^ (((kl.1 + kl.2 : ℕ) : ℝ) / 2)) * opFrob (opBlock X kl.1 kl.2)

/-- `X ∈ S = span{|g⟩⟨h| : g, h ∈ G}`: `X` has finitely many nonzero coefficients. -/
def InSpan {s : ℕ} (X : Op s) : Prop := (Function.support X).Finite

/-- Lemma 4.5, p.14: the contraction constant `λ = 3/4 + 24/√(2s)`. -/
noncomputable def lam (s : ℕ) : ℝ := 3 / 4 + 24 / Real.sqrt (2 * s)

end QuantumSymmetryBreaking.CycleColoring


