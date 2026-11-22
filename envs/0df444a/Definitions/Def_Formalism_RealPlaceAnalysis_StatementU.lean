-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
-- name    : Formalism_RealPlaceAnalysis_StatementU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:18.782749+00:00
-- url     : https://prove2.me/theorems/392067f1-37eb-4c0b-9b32-cc9628c5f741
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementU.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
def LamOf {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε
def cvalR {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ := nsq lam - nsq (rhoC ε + rhoN ε)
def KindA {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) : Prop :=
  KHighest ε E (LamOf ε lam) u ∧ Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u ∧
    FiniteDimensional ℂ (kSpan ε E u)
def Regime {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) : Prop :=
  (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧
    (n : ℝ) ^ 3 + 2 < 2 * g ∧ 2 * (n : ℝ) < g
def pfil {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ w : List (Fin n × Fin n), w.length ≤ j ∧ (∀ p ∈ w, ε p.1 ≠ ε p.2) ∧
    ∃ y ∈ kSpan ε E u, x = ew E w y}
def coinv {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (U : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ ({y | ∃ a b, a < b ∧ ε a = ε b ∧ ∃ x ∈ U, y = E b a x} ∪
    {y | ∃ a, ∃ x ∈ U, y = E a a x - ((Λ a : ℝ) : ℂ) • x})
abbrev Arr (V : Type*) (n j : ℕ) : Type _ := PiLp 2 (fun _ : Fin j → Fin n × Fin n => V)
def arrOf (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    Arr V n j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → V) :=
  (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).toLinearMap
def arrTo (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    ((Fin j → Fin n × Fin n) → V) →ₗ[ℂ] Arr V n j :=
  (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).symm.toLinearMap
def factorAction {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (i : Fin j) (c d : Fin n) :
    Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    (if (α i).1 = c then LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V)
        (Function.update α i (d, (α i).2)) else 0) -
    (if (α i).2 = d then LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V)
        (Function.update α i ((α i).1, c)) else 0)) ∘ₗ arrOf V n j
def ptE {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (c d : Fin n) : Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    E c d ∘ₗ LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α) ∘ₗ arrOf V n j
def arrE {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (j : ℕ) : Fin n → Fin n → Module.End ℂ (Arr V n j) :=
  fun c d => (∑ i : Fin j, factorAction i c d) + ptE E c d
def positionsE (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    Fin n → Fin n → Module.End ℂ (Arr V n j) :=
  fun c d => ∑ i : Fin j, factorAction i c d
def OmS {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) : Module.End ℂ (Arr V n j) :=
  ∑ c, ∑ d, if ε c = ε d then factorAction i c d * ptE E d c else 0
def thetaA {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (j : ℕ) : Arr V n j →ₗ[ℂ] V :=
  ∑ α : Fin j → Fin n × Fin n,
    ew E (List.ofFn α).reverse ∘ₗ LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ
      arrOf V n j
def permArr (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) {j : ℕ} (σ : Equiv.Perm (Fin j)) :
    Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) (fun i => α (σ i))) ∘ₗ arrOf V n j
def symSub (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) : Submodule ℂ (Arr V n j) :=
  ⨅ σ : Equiv.Perm (Fin j), LinearMap.ker (permArr V n σ - 1)
def arrV0 {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) : Submodule ℂ (Arr V n j) :=
  ⨅ α : Fin j → Fin n × Fin n,
    (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥).comap
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j)
def sliceLin (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) {j : ℕ} (α' : Fin j → Fin n × Fin n) :
    Arr V n (j + 1) →ₗ[ℂ] Arr V n 1 :=
  arrTo V n 1 ∘ₗ (LinearMap.pi fun β : Fin 1 → Fin n × Fin n =>
    LinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) → Fin n × Fin n => V)
      (Fin.cons (β 0) α' : Fin (j + 1) → Fin n × Fin n)) ∘ₗ arrOf V n (j + 1)
def Vplus {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) : Submodule ℂ (Arr V n 1) :=
  isoPart ε (arrE E 1) {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b} (arrV0 ε E u 1)
def Vminus {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) : Submodule ℂ (Arr V n 1) :=
  isoPart ε (arrE E 1) {μ | ∃ a b, b < a ∧ ε a ≠ ε b ∧ μ = Λ + root a b} (arrV0 ε E u 1)
def Nset {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ) :
    Submodule ℂ (Arr V n (j + 1)) :=
  arrV0 ε E u (j + 1) ⊓ symSub V n (j + 1) ⊓
    ⨅ α' : Fin j → Fin n × Fin n, (Vplus ε E Λ u).comap (sliceLin V n α')
def CasOnCyc : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ) (u : V),
    GlRel E → Cas E u = c • u → ∀ x ∈ cyc E u, Cas E x = c • x
def PfilFacts : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V),
    GlRel E →
    pfil ε E u 0 = kSpan ε E u ∧
    (∀ j, pfil ε E u j ≤ pfil ε E u (j + 1)) ∧
    (∀ j, KStable ε E (pfil ε E u j)) ∧
    (∀ j (a b : Fin n), ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1)) ∧
    (∀ j, pfil ε E u j ≤ cyc E u) ∧
    (∀ x ∈ cyc E u, ∃ j, x ∈ pfil ε E u j) ∧
    (FiniteDimensional ℂ (kSpan ε E u) → ∀ j, FiniteDimensional ℂ (pfil ε E u j))
def ArrModule : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ),
    (GlRel E → GlRel (arrE E j) ∧
      ∀ (c d : Fin n) (F : Arr V n j), thetaA E j (arrE E j c d F) = E c d (thetaA E j F)) ∧
    (IsUnitary ε E → KUnit ε (arrE E j))
def ThetaFil : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V),
    GlRel E →
    (∀ j, ∀ F ∈ arrV0 ε E u j, thetaA E j F ∈ pfil ε E u j) ∧
    (∀ j, pfil ε E u (j + 1) ≤ (arrV0 ε E u (j + 1)).map (thetaA E (j + 1)) ⊔ pfil ε E u j) ∧
    (∀ j, ∀ F ∈ arrV0 ε E u (j + 1), ∀ σ : Equiv.Perm (Fin (j + 1)),
      thetaA E (j + 1) (permArr V n σ F) - thetaA E (j + 1) F ∈ pfil ε E u j)
def HVCoeff : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ μ : Fin n → ℝ) (u : V) (F : Arr V n 1),
    GlRel E → IsUnitary ε E → KHighest ε E Λ u →
    F ∈ arrV0 ε E u 1 → KHighest ε (arrE E 1) μ F → F ≠ 0 →
    ∃ a b, ε a ≠ ε b ∧ μ = Λ + root a b
def TypesSplit : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ F ∈ Vplus ε E Λ u, ∀ G ∈ Vminus ε E Λ u, ⟪F, G⟫_ℂ = 0) ∧
    Vplus ε E Λ u ⊔ Vminus ε E Λ u = arrV0 ε E u 1
def ThetaMinus : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    ∀ F ∈ Vminus ε E (LamOf ε lam) u, thetaA E 1 F = 0
def OmPlus : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    ∀ F ∈ Vplus ε E (LamOf ε lam) u,
      (g - 2 * (n : ℝ)) * ‖F‖ ^ 2 ≤ (⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ).re
def CasArr : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ),
    (GlRel E → KHighest ε E Λ u → ∀ F ∈ arrV0 ε E u j,
      CasK ε (arrE E j) F = CasK ε (positionsE V n j) F + ((ckv ε Λ : ℝ) : ℂ) • F +
        (2 : ℂ) • ∑ i : Fin j, OmS ε E i F) ∧
    ∀ F : Arr V n j, 0 ≤ (⟪F, CasK ε (positionsE V n j) F⟫_ℂ).re
def OmSymSlice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) (F : Arr V n (j + 1)),
    (F ∈ symSub V n (j + 1) → ∀ i : Fin (j + 1), ⟪F, OmS ε E i F⟫_ℂ = ⟪F, OmS ε E 0 F⟫_ℂ) ∧
    ⟪F, OmS ε E 0 F⟫_ℂ =
      ∑ α' : Fin j → Fin n × Fin n, ⟪sliceLin V n α' F, OmS ε E (0 : Fin 1) (sliceLin V n α' F)⟫_ℂ
def NStable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ),
    KStable ε (arrE E (j + 1)) (Nset ε E Λ u j)
def NPos : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ),
    GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    ∀ F ∈ Nset ε E (LamOf ε lam) u j,
      (ckv ε (LamOf ε lam) + 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ))) * ‖F‖ ^ 2 ≤
        (⟪F, CasK ε (arrE E (j + 1)) F⟫_ℂ).re
def ThetaOntoN : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    ∀ F ∈ arrV0 ε E u (j + 1), ∃ F' ∈ Nset ε E (LamOf ε lam) u j,
      thetaA E (j + 1) F - thetaA E (j + 1) F' ∈ pfil ε E u j
def Mult1 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    ∀ x ∈ cyc E u, KHighest ε E (LamOf ε lam) x → ∃ c : ℂ, x = c • u
def Coinv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    ∀ x ∈ cyc E u, ∃ c : ℂ, x - c • u ∈ coinv ε E (LamOf ε lam) (cyc E u)
def CoinvFun : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (ℓ : V →ₗ[ℂ] ℂ),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    (∀ a b, a < b → ε a = ε b → ∀ x ∈ cyc E u, ℓ (E b a x) = 0) →
    (∀ a, ∀ x ∈ cyc E u, ℓ (E a a x) = ((LamOf ε lam a : ℝ) : ℂ) * ℓ x) →
    ∀ x ∈ cyc E u, ℓ x * ((‖u‖ ^ 2 : ℝ) : ℂ) = ℓ u * ⟪u, x⟫_ℂ
def InvFormUniq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    GlRel E → IsUnitary ε E → Regime ε lam g → KindA ε E lam u →
    (∀ a b, ∀ x ∈ cyc E u, ∀ y ∈ cyc E u, B (E a b x) y = (sgn ε a b : ℂ) * B x (E b a y)) →
    ∀ x ∈ cyc E u, ∀ y ∈ cyc E u, B x y * ((‖u‖ ^ 2 : ℝ) : ℂ) = B u u * ⟪x, y⟫_ℂ
def UnivGram : Prop :=
  ∀ (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (E' : Fin n → Fin n → Module.End ℂ V') (lam : Fin n → ℝ) (g : ℝ) (u : V) (u' : V'),
    GlRel E → IsUnitary ε E → GlRel E' → IsUnitary ε E' → Regime ε lam g →
    KindA ε E lam u → KindA ε E' lam u' → ‖u‖ = ‖u'‖ →
    ∀ w : List (Fin n × Fin n), ⟪u, ew E w u⟫_ℂ = ⟪u', ew E' w u'⟫_ℂ
def UIso : Prop :=
  ∀ (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (E' : Fin n → Fin n → Module.End ℂ V') (lam : Fin n → ℝ) (g : ℝ) (u : V) (u' : V'),
    GlRel E → IsUnitary ε E → GlRel E' → IsUnitary ε E' → Regime ε lam g →
    KindA ε E lam u → KindA ε E' lam u' → ‖u‖ = ‖u'‖ →
    ∃ T : V →ₗ[ℂ] V', T u = u' ∧
      (∀ x ∈ cyc E u, T x ∈ cyc E' u' ∧ ∀ a b, T (E a b x) = E' a b (T x)) ∧
      (∀ x ∈ cyc E u, ∀ y ∈ cyc E u, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      cyc E' u' ≤ (cyc E u).map T
def UGrowth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (c : ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E μ u → Cas E u = (c : ℂ) • u →
    FiniteDimensional ℂ (kSpan ε E u) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ b, ‖E a b x‖ ^ 2 ≤
        (2 * (n : ℝ) * (Real.sqrt (ckv ε μ) + j + n) ^ 2 + |c|) * ‖x‖ ^ 2
end Formalism.REAL


