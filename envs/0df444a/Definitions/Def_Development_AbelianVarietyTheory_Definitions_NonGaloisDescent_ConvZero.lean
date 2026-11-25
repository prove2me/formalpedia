-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConvZero
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConvZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:51.885796+00:00
-- url     : https://prove2.me/theorems/d9197483-6009-4999-b0ca-3946cfeb0ca2
-- title:
--   Conv Zero
-- statement:
--   Definitions and structural lemmas for Conv Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConvZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HWL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
variable {l : ℕ} [Fact l.Prime]
def FaithH {P : LocPrime l} (AI : LocAinf l P) : Prop :=
  ∀ (L : FinExt l) (g : GQ l), P.χQ g = 1 →
    (∀ x : OCb l, (∀ h ∈ GK L, P.χQ h = 1 → AI.actT h x = x) → AI.actT g x = x) → g ∈ GK L
variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
def FixH (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l} (x : RW LL) : Prop :=
  ∀ g ∈ GK K, P.χQ g = 1 → AI.gRW LL g x = x
def FixBasis (AI : LocAinf l P) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {r : ℕ}
    (e : Module.Basis (Fin r) (RW LL) (TW (RW LL) T)) : Prop :=
  ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (e i) = e i
def EtBasis {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {r : ℕ}
    (e : Module.Basis (Fin r) (RW LL) (TW (RW LL) T)) : Prop :=
  FixBasis AI T e ∧ ∀ i j, e.repr (TWmap (φRW LL) T (e j)) i ∈ Set.range I.ioE
def WachEx {P : LocPrime l} (AI : LocAinf l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ E : WEt I, Nonempty (NS E)
def Conv (a : PowerSeries ↥LL.1) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k a : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)
def IsExp (ζ : ↥LL.1) (a e : PowerSeries ↥LL.1) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => ((PowerSeries.coeff k
    (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) (PowerSeries.trunc m a)) : ↥LL.1) : Om l))
    Filter.atTop (nhds ((PowerSeries.coeff k e : ↥LL.1) : Om l))
def logS (LL : FinExt l) : PowerSeries ↥LL.1 :=
  PowerSeries.mk fun k => (-1 : ↥LL.1) ^ (k + 1) / (k : ↥LL.1)
def toLL {n : ℕ} (a : LetA ↥(OL LL) n) : LetA ↥LL.1 n :=
  fun i => PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (a i)
def IsBeta (AI : LocAinf l P) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) : Prop :=
  ∀ (o : ↥(OL LL)) (w : Ainf l), β (o ⊗ₜ[ℤ_[l]] w) = (o : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w
structure IsEval {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B)
    (J : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1 ⊗[ℚ_[l]] P.R.B) : Prop where
  add : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a + b) = J a + J b
  mul : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a * b) = J a * J b
  smul : ∀ (c : ↥LL.1) a, (∀ i, Conv (a i)) → J (c • a) = c • J a
  ext : ∀ a, J (toLL a) = β (I.io a)
  frob : ∀ a, (∀ i, Conv (a i)) →
    J (fun i => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (i - 1))) =
      Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (J a)
  gal : ∀ (g : ↥(GK K)) a, (∀ i, Conv (a i)) →
    J (fun i => PowerSeries.subst
        (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ (Γ.resΓ g) PowerSeries.X)) (a i)) =
      Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ (g : GQ l)).toAlgHom (J a)
  log : J (fun _ => logS LL) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ s)⁻¹) • P.tB)
  taylor : ∀ i (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR),
    (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) →
    ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ a, (∀ j, Conv (a j)) → ∀ e, IsExp ζ (a i) e → ∀ m : ℕ,
    Algebra.TensorProduct.productMap ι P.ιB (J a) -
      ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k e) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈
        (P.PD K).Fil (m : ℤ)
def TateSen (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)),
    (∀ (g : GQ l) (x : Om l), act g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)) →
    (∀ (g : GQ l) (y : PadicComplex l), ‖act g y‖ = ‖y‖) →
    ∀ (K : FinExt l) (η : ↥(GK K) →* ℤ_[l]ˣ), Continuous η → (η '' (IK K : Set ↥(GK K))).Infinite →
    ∀ z : PadicComplex l,
      (∀ g : ↥(GK K), act (g : GQ l) z = algebraMap ℚ_[l] (PadicComplex l) ((η g : ℤ_[l]) : ℚ_[l]) * z) → z = 0
def Regular (P : LocPrime l) : Prop :=
  ∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b
end GlobalTheory.HWL


