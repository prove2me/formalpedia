-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_factorMat
-- name    : GroupIsoPoly_Supplement_factorMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:27:15.810979+00:00
-- url     : https://prove2.me/theorems/4cda466e-cc5b-4612-843e-783ba9f491d6
-- title:
--   Products of classical groups and their modules; restriction of scalars
-- statement:
--   Let $D=\prod_{i<t}G_i$ be a product of classical groups $G_i\le\mathrm{GL}(n_i,K_i)$ (the fields may differ). The module of kind $\kappa$ of the factor $i$ is pulled back to $D$ along the projection: $g\in D$ acts by the matrix of $g_i$ on that module.
--
--   A family of matrices $\rho(g)\in\mathrm{Mat}(a,L)$ is a **realization after restriction of scalars** of that module if there are a field embedding $\iota:L\to K_i$ and an additive bijection $e:L^a\to K_i^{n_i}$ with $e(cx)=\iota(c)e(x)$ and $e(\rho(g)x)=g_i\cdot e(x)$ for all $g\in D$; that is, $\rho$ is the matrix of the action of $D$ on the module viewed as an $L$-vector space, in some $L$-basis.
--
--   These describe "a natural, dual, or Frobenius-twisted module of one factor of $D$" (Definition 16) and modules "viewed over $\mathbb F_p$ by restriction of scalars" (Theorem C.9).
--
--   **Formalization Note** The $L$-basis is existentially quantified, so every matrix realization qualifies; with $L=K_i$ and $e=\mathrm{id}$ the module realizes itself.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 16, p.48 (PDF p.52); Definition 14, p.46 (PDF p.50); Theorem C.9, p.146 (PDF p.150)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_classicalGroup
import Definitions.Def_GroupIsoPoly_Supplement_stdMat

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

open Matrix

/-- The product `D = ∏_{i<t} G_i` of the classical groups `G_i = classicalGroup (dat i) ≤ GL(n_i, K_i)`
(the fields `K_i` may differ). -/
abbrev ClProd {t : ℕ} {K : Fin t → Type} [∀ i, Field (K i)] {n : Fin t → ℕ}
    (dat : (i : Fin t) → ClassicalDatum (K i) (n i)) : Type :=
  (i : Fin t) → classicalGroup (dat i)

/-- **The action of the product `D` on a natural, dual or Frobenius-twisted module of one factor.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 16, p.48 (PDF p.52): "each Ti is a natural,
dual, or Frobenius-twisted module of one factor of D"; Theorem C.9, p.146 (PDF p.150).

`factorMat dat i κ g` is the matrix of `g ∈ D` on the module of kind `κ` of the factor `i`: the
module is pulled back along the projection `D → G_i`, so `g` acts by `stdMat κ (g_i)`. -/
noncomputable def factorMat {t : ℕ} {K : Fin t → Type} [∀ i, Field (K i)] {n : Fin t → ℕ}
    (dat : (i : Fin t) → ClassicalDatum (K i) (n i)) (i : Fin t) (κ : ModKind) (g : ClProd dat) :
    Matrix (Fin (n i)) (Fin (n i)) (K i) :=
  stdMat κ ((g i : classicalGroup (dat i)) : GL (Fin (n i)) (K i))

/-- **A matrix realization of a module of one factor after restriction of scalars.**

`IsRestrictionOf dat i κ ρ` says that the matrices `ρ g ∈ Mat(a, L)` are the matrices of the action
of `D` on the module of kind `κ` of the factor `i`, viewed over a subfield `L` of `K_i` by
restriction of scalars, in some `L`-basis: there are a field embedding `ι : L → K_i` and an additive
bijection `e : L^a → K_i^{n_i}` with `e(c x) = ι(c) e(x)` and `e(ρ(g) x) = factorMat dat i κ g (e x)`.

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 14, p.46 (PDF p.50):
"explicitly represented natural, dual, Frobenius-twisted, or trivial modules, with restriction of
scalars where required"; Theorem C.9, p.146 (PDF p.150): "viewed over Fp by restriction of scalars".

**Formalization Note.** The basis is existentially quantified: every matrix realization in every
`L`-basis qualifies. With `L = K_i`, `ι = id` and `e = id` this is the module itself. -/
def IsRestrictionOf {t : ℕ} {K : Fin t → Type} [∀ i, Field (K i)] {n : Fin t → ℕ}
    (dat : (i : Fin t) → ClassicalDatum (K i) (n i)) (i : Fin t) (κ : ModKind)
    {L : Type} [Field L] {a : ℕ} (ρ : ClProd dat → Matrix (Fin a) (Fin a) L) : Prop :=
  ∃ (ι : L →+* K i) (e : (Fin a → L) ≃+ (Fin (n i) → K i)),
    (∀ (c : L) (x : Fin a → L), e (c • x) = ι c • e x) ∧
    ∀ (g : ClProd dat) (x : Fin a → L), e (ρ g *ᵥ x) = factorMat dat i κ g *ᵥ e x

end Supplement

end GroupIsoPoly


