-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul
-- name    : ExplicitTensorBarrier694_Explicit_Koszul
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:45.241898+00:00
-- url     : https://prove2.me/theorems/b33a7df1-6f03-48ca-ab78-7ed51454cf64
-- title:
--   Koszul matrices and rank-one normalization
-- statement:
--   For a tensor $T\in\mathbb C^a\otimes\mathbb C^b\otimes\mathbb C^c$ and $0\le p<a$, the Koszul map is
--
--   $$K_p(x\otimes y\otimes z)(\omega\otimes\varphi)=(x\wedge\omega)\otimes\varphi(y)z.$$
--
--   Its matrix has columns $(I,u)$ for $p$-subsets $I$ and rows $(J,v)$ for $(p+1)$-subsets $J$. A contribution from coordinate $\ell$ is zero unless $\ell\notin I$ and $J=I\cup\{\ell\}$; otherwise it is $(-1)^{|\{i\in I:i<\ell\}|}T_{\ell uv}$. This sign specifies the source's left wedge. Define $\rho(K_p)$ as the maximum matrix rank on all pure tensors. This maximum exists because ranks are natural numbers bounded by the finite matrix dimensions. Invertibility means bijectivity of the induced linear map, including when the two basis index types differ.
--
--   For $s=2e-1$, general position of a collection of $s$ vectors in $\mathbb C^e$ means independence of every indexed $e$-subset. Given any basis $z_\ell$ of $\mathbb C^s$ and collections $b_\ell,c_\ell$, the associated tensor is $\sum_\ell z_\ell\otimes b_\ell\otimes c_\ell$. These definitions encode the full map and general-position data rather than assuming any rank conclusion.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Definition 2.2 p.6, equation (1.2) p.2, and Lemma 3.1 setup p.7 (PDF same pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit

/-- Increasing exterior-basis indices; the empty set indexes Λ⁰. -/
abbrev WedgeIndex (a p : ℕ) := {I : Finset (Fin a) // I.card = p}

/-- Definition 2.2, p.6, in increasing exterior bases. Rows are (J,v), columns
(I,u). The sign counts indices of I smaller than l, because the source wedges
on the LEFT: z_l ∧ z_I. This is a matrix of the actual Koszul map, for any p. -/
noncomputable def koszul {a b c : ℕ} (p : ℕ) (T : Tensor a b c) :
    Matrix (WedgeIndex a (p + 1) × Fin c) (WedgeIndex a p × Fin b) ℂ := by
  classical
  exact fun row col => ∑ l : Fin a,
    if l ∉ col.1.val ∧ insert l col.1.val = row.1.val then
      (-1 : ℂ) ^ (col.1.val.filter (fun i => i < l)).card * T l col.2 row.2
    else 0

/-- Maximum rank on pure tensors, including zero factors (p.2, Proposition 2.3).
The set is nonempty (zero factors) and bounded by the finite matrix dimensions. -/
noncomputable def koszulRho (a b c p : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ (x : Fin a → ℂ) (y : Fin b → ℂ) (z : Fin c → ℂ),
    (koszul p (pure x y z)).rank = r}

/-- Invertibility as a bijective linear map; the row and column exterior bases
have different index types, even when the dimensions coincide. -/
noncomputable def KoszulInvertible {a b c : ℕ} (p : ℕ) (T : Tensor a b c) : Prop :=
  Function.Bijective (koszul p T).mulVecLin

/-- Every e-element indexed subcollection is independent, with no assumption
about the other collection hidden here (Lemma 3.1). -/
def GeneralPosition {s e : ℕ} (v : Fin s → Fin e → ℂ) : Prop :=
  ∀ I : Finset (Fin s), I.card = e → LinearIndependent ℂ (fun l : I => v l.val)

/-- The tensor of Lemma 3.1 for any basis z, not just the standard basis. -/
noncomputable def generalPositionTensor {e : ℕ}
    (z : Module.Basis (Fin (2 * e - 1)) ℂ (Fin (2 * e - 1) → ℂ))
    (b c : Fin (2 * e - 1) → Fin e → ℂ) : Tensor (2 * e - 1) e e :=
  ∑ l, pure (z l) (b l) (c l)

end ExplicitTensorBarrier694.Explicit


