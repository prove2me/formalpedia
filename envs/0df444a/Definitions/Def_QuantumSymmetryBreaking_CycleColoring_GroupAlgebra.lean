-- Prove2me | Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra
-- name    : QuantumSymmetryBreaking_CycleColoring_GroupAlgebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:33.720966+00:00
-- url     : https://prove2.me/theorems/b3db1c33-d113-4d4c-887d-1772adf89c6e
-- title:
--   §4.2 — the group algebra $\mathbb C[G\times G]$, vectorization, $K_{\pm i}$, $S'$ and the norms
-- statement:
--   $\mathbb C[G\times G]$ is the complex group algebra of $G\times G$: finite linear combinations of indeterminates $[g,h]$, $g,h\in G$, multiplied by
--   $$
--   [g,h]\cdot[g',h']=[gg',hh'] .
--   $$
--   Its unit is $[e,e]$. For an operator $Z\in\mathcal S$ the vectorization is $Z'=\sum_{g,h}Z(g,h)[g,h]$ (Definition 4.9). The adjoint is $X^*=\sum_{g,h}\overline{X(g,h)}\,[g^{-1},h^{-1}]$, and $X$ is self-adjoint when $X^*=X$. For each letter $i$,
--   $$
--   K_{+i}=\tfrac14([e,e]+[i,e])([e,e]-[e,i]),\qquad K_{-i}=\tfrac14([e,e]-[i,e])([e,e]+[e,i]),
--   $$
--   where $[i,e]$ means $[g_i,e]$, and
--   $$
--   S'(X)=\sum_{i\in[s]}\bigl(K_{+i}XK_{+i}+K_{-i}XK_{-i}\bigr).
--   $$
--   The Frobenius norm is $\|X\|_F=(\sum_{g,h}|X(g,h)|^2)^{1/2}$ and the weighted norm is $\|X\|_w=\sum_{k,\ell}2^{(k+\ell)/2}\|X_{k,\ell}\|_F$, with $X_{k,\ell}$ the part of $X$ supported on $|g|=k$, $|h|=\ell$. Finally, for Proposition 4.12, $\binom{\alpha}{j}=\alpha(\alpha-1)\cdots(\alpha-j+1)/j!$ and $X_k=\sum_{j=0}^k\binom{1/2}{j}C^j$.
--
--   The vectorization changes the multiplicative structure from operator composition to the group law of $G\times G$, which is the structure that finite-dimensional representations $[g,h]\mapsto U_g\otimes U_h$ preserve (§5.2).
--
--   **Formalization Note** $\mathbb C[G\times G]$ is Mathlib's `MonoidAlgebra ℂ (G s × G s)`. The vectorization `vec` is defined for coefficient arrays with finitely many nonzero entries and returns $0$ (a placeholder) otherwise. The adjoint conjugates the coefficients, as in the proof of Lemma 4.10 (p.19) and footnote 3 (p.23). The weighted norm on $\mathbb C[G\times G]$ is the formula of Proposition 4.4 applied to coefficients, as the source uses it implicitly in §4.2.
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, §4.2 pp.18–20: Definition 4.9 p.18, Lemma 4.10 p.18 and its proof p.19, Frobenius norm and S′ p.19, footnote 3 p.23, Proposition 4.12 p.20 — PDF pp.21–23, 26

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction

/-!
# The vectorized construction in the group algebra `ℂ[G × G]`

Maxime Flin, Longcheng Li, Jukka Suomela, *Quantum Advantage for Distributed Symmetry Breaking*,
STOC 2027 submission #863 (October 2026), §4.2 pp.18–20: Definition 4.9 (`ℂ[G × G]` and the
vectorization `Z ↦ Z′`), Lemma 4.10 (the elements `K_{±i}` and the adjoint), the Frobenius norm on
`ℂ[G × G]` and the map `S′` (p.19), the weighted norm on `ℂ[G × G]` (§4.2, used in Lemma 4.11), and the
generalized binomial coefficient of Proposition 4.12 (p.20).

`ℂ[G × G]` is Mathlib's `MonoidAlgebra ℂ (G × G)`: finitely supported coefficient functions with the
convolution product, so `[g, h] · [g′, h′] = [g g′, h h′]`.
-/

namespace QuantumSymmetryBreaking.CycleColoring

/-- Definition 4.9, p.18: the group algebra `ℂ[G × G]`. -/
abbrev Alg (s : ℕ) : Type := MonoidAlgebra ℂ (G s × G s)

/-- Definition 4.9: the indeterminate `[g, h] ∈ ℂ[G × G]`. -/
noncomputable def br {s : ℕ} (g h : G s) : Alg s := MonoidAlgebra.single (g, h) 1

open Classical in
/-- Definition 4.9, p.18: the vectorization `Z′ = ∑_{g,h} Z(g,h) [g, h]` of an operator
`Z ∈ S = span{|g⟩⟨h|}`. It is defined for `Z` with finitely many nonzero coefficients (`InSpan Z`);
outside `S` the source leaves `Z′` undefined and the value `0` is a placeholder. -/
noncomputable def vec {s : ℕ} (Z : Op s) : Alg s :=
  if h : InSpan Z then MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite Z h) else 0

/-- Proof of Lemma 4.10 p.19 and footnote 3 p.23: the adjoint
`X* = ∑_{g,h} \overline{X(g,h)} [g⁻¹, h⁻¹]` (conjugate-linear). -/
noncomputable def algStar {s : ℕ} (X : Alg s) : Alg s :=
  X.coeff.sum fun p c => MonoidAlgebra.single (p.1⁻¹, p.2⁻¹) (star c)

/-- `X ∈ ℂ[G × G]` is self-adjoint: `X* = X`. -/
def IsSelfAdj {s : ℕ} (X : Alg s) : Prop := algStar X = X

/-- Lemma 4.10, p.18: `K_{+i} = ([e, e] + [i, e])([e, e] - [e, i])/4`. -/
noncomputable def Kplus {s : ℕ} (i : Fin s) : Alg s :=
  (1 / 4 : ℂ) • ((br 1 1 + br (gen s i) 1) * (br 1 1 - br 1 (gen s i)))

/-- Lemma 4.10, p.18: `K_{-i} = ([e, e] - [i, e])([e, e] + [e, i])/4`. -/
noncomputable def Kminus {s : ℕ} (i : Fin s) : Alg s :=
  (1 / 4 : ℂ) • ((br 1 1 - br (gen s i) 1) * (br 1 1 + br 1 (gen s i)))

/-- §4.2, p.19: `S′(X) = ∑_{i ∈ [s]} (K_{+i} X K_{+i} + K_{-i} X K_{-i})`. -/
noncomputable def Sprime {s : ℕ} (X : Alg s) : Alg s :=
  ∑ i : Fin s, (Kplus i * X * Kplus i + Kminus i * X * Kminus i)

/-- §4.2, p.19: the Frobenius norm `‖X‖_F = (∑_{g,h} |X(g,h)|²)^{1/2}` on `ℂ[G × G]`. -/
noncomputable def algFrob {s : ℕ} (X : Alg s) : ℝ :=
  Real.sqrt (∑ p ∈ X.coeff.support, ‖X.coeff p‖ ^ 2)

open Classical in
/-- The block `X_{k,ℓ} = ∑_{|g| = k, |h| = ℓ} X(g,h) [g, h]` of `X ∈ ℂ[G × G]`. -/
noncomputable def algBlock {s : ℕ} (X : Alg s) (k l : ℕ) : Alg s :=
  MonoidAlgebra.ofCoeff (X.coeff.filter fun p => len p.1 = k ∧ len p.2 = l)

/-- Proposition 4.4 p.14, transported to `ℂ[G × G]` (§4.2): the weighted norm
`‖X‖_w = ∑_{k,ℓ ≥ 0} 2^{(k+ℓ)/2} ‖X_{k,ℓ}‖_F`. Only the finitely many pairs `(k, ℓ)` that occur as
`(|g|, |h|)` for `(g, h)` in the support of `X` have a nonzero block, so the sum is over those. -/
noncomputable def algW {s : ℕ} (X : Alg s) : ℝ :=
  ∑ kl ∈ X.coeff.support.image (fun p => (len p.1, len p.2)),
    (2 : ℝ) ^ (((kl.1 + kl.2 : ℕ) : ℝ) / 2) * algFrob (algBlock X kl.1 kl.2)

/-- Proposition 4.12, p.20: the generalized binomial coefficient
`(α choose j) = α(α - 1)(α - 2)⋯(α - j + 1)/j!`. -/
noncomputable def genChoose (α : ℝ) (j : ℕ) : ℝ :=
  (∏ m ∈ Finset.range j, (α - m)) / (j.factorial : ℝ)

/-- Proposition 4.12, p.20: the partial binomial series `X = ∑_{j=0}^{k} (1/2 choose j) C^j`. -/
noncomputable def sqrtPartial {s : ℕ} (C : Alg s) (k : ℕ) : Alg s :=
  ∑ j ∈ Finset.range (k + 1), ((genChoose (1 / 2) j : ℝ) : ℂ) • C ^ j

end QuantumSymmetryBreaking.CycleColoring


