-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
-- name    : ReciprocityTheory_DualLattices_HtLinStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:44.171094+00:00
-- url     : https://prove2.me/theorems/dfc1628a-3e35-4255-b324-14cdffce2ee0
-- title:
--   Ht Lin Statement
-- statement:
--   Definitions and structural lemmas for Ht Lin Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HtLinStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
structure ATowerL (R₀ : Type u) [CommRing R₀] (p : ℕ) extends ATower R₀ p where
  r' : ∀ n, LHom (R' (n + 1)) (R' n)
  r : ∀ n, LHom (R (n + 1)) (R n)
  r_π : ∀ n (x : (R' (n + 1) : Type u)), (r n).1 ((π (n + 1)).1 x) = (π n).1 ((r' n).1 x)
  r_q : ∀ n (x : (O : Type u)), (r n).1 ((q (n + 1)).1 x) = (q n).1 x
  r'_ξ : ∀ n, (r' n).1 (ξ (n + 1)) = ξ n
  complete : ∀ x : ∀ n, (R n : Type u), (∀ n, (r n).1 (x (n + 1)) = x n) →
    ∃ a : (O : Type u), ∀ n, (q n).1 a = x n
variable {R₀ : Type u} [CommRing R₀]
structure DualTower {p : ℕ} (Tw : ATowerL R₀ p) where
  Dp : ∀ n, DualPair (Tw.R n)
  d : ∀ n, LHom (Dp (n + 1)).D (Dp n).D
  d_π : ∀ n (x : ((Dp (n + 1)).D : Type u)), (Dp n).π.1 ((d n).1 x) = (Tw.r n).1 ((Dp (n + 1)).π.1 x)
  d_σ : ∀ n (x : (Tw.R (n + 1) : Type u)), (d n).1 ((Dp (n + 1)).σ.1 x) = (Dp n).σ.1 ((Tw.r n).1 x)
  d_η : ∀ n, (d n).1 (Dp (n + 1)).η = (Dp n).η
def LimStatement (B : BX R₀) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) : Prop :=
  ∀ (ι : Type) (τ : ι → ℕ → B.G Tw.O),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    ∃ (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u)) (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
      (∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
        ((Tw.q n).1.toLinearMap ∘ₗ ht i)) ∧
      (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
        B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
        (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
          (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
          LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i))
def HtLinStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) : Prop :=
  ∀ (ι : Type) [Fintype ι] (τ : ι → ℕ → B.G Tw.O) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (a : ι → ℕ → ℤ) (α : ι → (Tw.O : Type u)),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, (Tw.q n).1 (α i) = a i n) →
    ∀ n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (∑ i, a i n • τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i)
end ReciprocityTheory.PGsh


