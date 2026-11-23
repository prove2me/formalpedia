-- Prove2me | Definitions.Def_Formalism_SharpRestriction_ValuationFrobeniusEpsilon_LiftInvariantsFinrankEq
-- name    : Formalism_SharpRestriction_ValuationFrobeniusEpsilon_LiftInvariantsFinrankEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:26.860672+00:00
-- url     : https://prove2.me/theorems/01a2f504-6804-4fd7-b87f-bd7adf0cbdb1
-- title:
--   Lift Invariants Finrank Eq
-- statement:
--   Definitions and structural lemmas for Lift Invariants Finrank Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LiftInvariantsFinrankEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.V1
open IsLocalRing MvPowerSeries
open scoped Classical
class IsCNL (O : Type) (A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)
attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom
structure TR (O : Type) [CommRing O] [IsLocalRing O] where
  C : Type
  [cr : CommRing C]
  [lr : IsLocalRing C]
  [al : Algebra O C]
  [cnl : IsCNL O C]
attribute [instance] TR.cr TR.lr TR.al TR.cnl
abbrev Wt (r : ℕ) : Type := Fin r → ℤ
abbrev TA (r : ℕ) (A : Type) [CommRing A] : Type := MvPowerSeries (Fin r) A
def onePlusT (r : ℕ) (A : Type) [CommRing A] (s : Fin r) : (TA r A)ˣ :=
  (MvPowerSeries.isUnit_iff_constantCoeff.mpr
    (by simp : IsUnit (constantCoeff (1 + X s : TA r A)))).unit
def tpowT (r : ℕ) (A : Type) [CommRing A] (j : Wt r) : (TA r A)ˣ :=
  ∏ s, onePlusT r A s ^ (j s)
def tpow {A : Type} [CommRing A] {r : ℕ} (t : Fin r → Aˣ) (j : Wt r) : A :=
  ((∏ s, t s ^ j s : Aˣ) : A)
def IsEigen {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (c : A →ₐ[O] TA r A)
    (j : Wt r) (x : A) : Prop :=
  c x = (tpowT r A j : TA r A) * MvPowerSeries.C x
inductive GGKind | typeThree | typeTwo | GSp4
  deriving DecidableEq
def GGKind.n : GGKind → ℕ
  | .typeThree => 3
  | .typeTwo => 2
  | .GSp4 => 4
def GGKind.dimN : GGKind → ℕ
  | .typeThree => 9
  | .typeTwo => 4
  | .GSp4 => 10
def Jsp (A : Type) [CommRing A] : Matrix (Fin 4) (Fin 4) A :=
  Matrix.of fun i j => if (i : ℕ) + j = 3 then (if (i : ℕ) < 2 then 1 else -1) else 0
def GGKind.Sympl (κ : GGKind) {A : Type} [CommRing A] (g : Matrix (Fin κ.n) (Fin κ.n) A) (ν : A) :
    Prop :=
  ∃ h : κ.n = 4, (Matrix.reindex (finCongr h) (finCongr h) g).transpose * Jsp A *
    Matrix.reindex (finCongr h) (finCongr h) g = ν • Jsp A
def GGKind.InG (κ : GGKind) {A : Type} [CommRing A] (g : Matrix (Fin κ.n) (Fin κ.n) A) : Prop :=
  IsUnit g.det ∧ (κ = .GSp4 → ∃ ν : Aˣ, κ.Sympl g ν)
def resMat {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (x : Matrix (Fin n) (Fin n) C) :
    Matrix (Fin n) (Fin n) (ResidueField C) := x.map (residue C)
def kToRes {O C : Type} [CommRing O] [IsLocalRing O] [CommRing C] [IsLocalRing C] [Algebra O C]
    [IsLocalHom (algebraMap O C)] : ResidueField O →+* ResidueField C :=
  ResidueField.map (algebraMap O C)
def IsLiftG {O G : Type} [CommRing O] [IsLocalRing O] [Group G] [TopologicalSpace G] (κ : GGKind)
    (GF : Subgroup G) (chi : G →* Oˣ) (U : G → Prop)
    (r0 : G → Matrix (Fin κ.n) (Fin κ.n) (ResidueField O)) {C : Type} [CommRing C] [IsLocalRing C]
    [Algebra O C] [IsLocalHom (algebraMap O C)] (r : G → Matrix (Fin κ.n) (Fin κ.n) C) : Prop :=
  (∀ g, IsUnit (r g).det) ∧
  (∀ g h, r (g * h) = r g * (if g ∈ GF then r h else
    algebraMap O C (chi h : O) • ((r h)⁻¹).transpose)) ∧
  (κ = .GSp4 → ∀ g, κ.Sympl (r g) (algebraMap O C (chi g : O))) ∧
  (∀ (N : ℕ) (g0 : G), ∀ᶠ g in nhds g0, ∀ i j, r g i j - r g0 i j ∈ maximalIdeal C ^ N) ∧
  (∀ g, resMat (r g) = (r0 g).map kToRes) ∧
  (∀ g, U g → r g = 1)
def IsKerEl (κ : GGKind) {C : Type} [CommRing C] [IsLocalRing C]
    (γ : Matrix (Fin κ.n) (Fin κ.n) C) : Prop := κ.InG γ ∧ resMat γ = 1
def ConjG {G C : Type} [Group G] [CommRing C] {n : ℕ} (GF : Subgroup G)
    (γ : Matrix (Fin n) (Fin n) C) (r r' : G → Matrix (Fin n) (Fin n) C) : Prop :=
  ∀ g, r' g = γ * r g * (if g ∈ GF then γ⁻¹ else γ.transpose)
def diagT {C : Type} [CommRing C] {n r : ℕ} (dg : Fin n → Wt r) (t : Fin r → Cˣ) :
    Matrix (Fin n) (Fin n) C := Matrix.diagonal fun i => tpow t (dg i)
def diagTT {n r : ℕ} (dg : Fin n → Wt r) (A : Type) [CommRing A] : Matrix (Fin n) (Fin n) (TA r A) :=
  Matrix.diagonal fun i => (tpowT r A (dg i) : TA r A)
def nEqG {O G C : Type} [CommRing O] [CommRing C] [Algebra O C] {n : ℕ} (x : G →₀ O)
    (pos : Fin n × Fin n) (c : O) (r : G → Matrix (Fin n) (Fin n) C) : C :=
  ((x.sum fun g a => a • r g) pos.1 pos.2) - algebraMap O C c
def gLie (k : Type) [Field k] : (κ : GGKind) → Submodule k (Matrix (Fin κ.n) (Fin κ.n) k)
  | .GSp4 => LinearMap.ker ((LinearMap.mulRight k (Jsp k)).comp
      (Matrix.transposeLinearEquiv (Fin 4) (Fin 4) k k).toLinearMap + LinearMap.mulLeft k (Jsp k))
  | .typeThree => ⊤
  | .typeTwo => ⊤
def adAct {G k : Type} [Group G] [Field k] {n : ℕ} (GF : Subgroup G)
    (r0 : G → Matrix (Fin n) (Fin n) k) (g : G) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun X := if g ∈ GF then r0 g * X * (r0 g)⁻¹ else -(r0 g * X.transpose * (r0 g)⁻¹)
  map_add' X Y := by
    split_ifs <;> simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, add_comm]
  map_smul' c X := by
    split_ifs <;> simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul]
def invSub {G k : Type} [Field k] {n : ℕ} (act : G → Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k)
    (N : Submodule k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) :=
  N ⊓ ⨅ g, LinearMap.ker (act g - LinearMap.id)
def MazurFin (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : OpenSubgroup G, Finite (ContinuousMonoidHom H (Multiplicative (ZMod l)))
end Formalism.BasicNotions.V1
namespace Formalism.BasicNotions.V1
open IsLocalRing MvPowerSeries
open scoped Classical
structure LiftProb where
  l : ℕ
  l_prime : l.Prime
  l_odd : l ≠ 2

  O : Type
  [oR : CommRing O]
  [oD : IsDomain O]
  [oV : IsDiscreteValuationRing O]
  [oC : IsAdicComplete (maximalIdeal O) O]
  [o0 : CharZero O]
  [oF : Finite (ResidueField O)]
  [oP : CharP (ResidueField O) l]

  Gam : Type
  [gG : Group Gam]
  [gT : TopologicalSpace Gam]
  [gTG : IsTopologicalGroup Gam]
  [gC : CompactSpace Gam]
  [gTD : TotallyDisconnectedSpace Gam]
  mazur : MazurFin l Gam
  kind : GGKind

  GF : Subgroup Gam
  GF_top : kind = .GSp4 → GF = ⊤
  GF_index : kind ≠ .GSp4 → GF.index = 2
  GF_open : IsOpen (GF : Set Gam)

  cc : Gam
  cc_sq : cc * cc = 1
  cc_out : kind ≠ .GSp4 → cc ∉ GF

  lPl : Type
  [lF : Fintype lPl]
  lPl_ne : Nonempty lPl
  Gv : lPl → Subgroup Gam
  Gv_closed : ∀ v, IsClosed (Gv v : Set Gam)

  qPl : Type
  [qF : Fintype qPl]
  Gq : qPl → Subgroup Gam
  Iq : qPl → Subgroup Gam
  Iq_le : ∀ q, Iq q ≤ Gq q
  Gq_closed : ∀ q, IsClosed (Gq q : Set Gam)
  Iq_closed : ∀ q, IsClosed (Iq q : Set Gam)

  rPl : Type
  [rF : Fintype rPl]
  cv : rPl → Gam
  cv_sq : ∀ v, cv v * cv v = 1

  degF : ℕ
  degF_eq : degF = Fintype.card rPl

  dv : lPl → ℕ
  dv_sum : ∑ v, dv v = degF

  Iq_normal : ∀ q, ∀ g ∈ Gq q, ∀ h ∈ Iq q, g * h * g⁻¹ ∈ Iq q

  isQ : Prop
  isQ_deg : isQ ↔ degF = 1

  chi : Gam →* Oˣ

  chi_cont : ∀ (N : ℕ) (g0 : Gam), ∀ᶠ g in nhds g0, ((chi g : Oˣ) : O) - ((chi g0 : Oˣ) : O) ∈ maximalIdeal O ^ N

  cyc : Gam →* (ResidueField O)ˣ

  rk : ℕ

  dg : Fin kind.n → Wt rk

  faithful : AddSubgroup.closure (Set.range fun p : Fin kind.n × Fin kind.n => dg p.1 - dg p.2) = ⊤

  rbar : Gam → Matrix (Fin kind.n) (Fin kind.n) (ResidueField O)

  chi_Uq : ∀ g, (∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) → chi g = 1
  rbar_hom : ∀ g h, rbar (g * h) = rbar g * (if g ∈ GF then rbar h else
    residue O (chi h : O) • ((rbar h)⁻¹).transpose)
  rbar_unit : ∀ g, IsUnit (rbar g).det
  rbar_sympl : kind = .GSp4 → ∀ g, kind.Sympl (rbar g) (residue O (chi g : O))
  rbar_cont : IsLocallyConstant rbar

  rbar_diag : ∀ g ∈ GF, ∀ i j, i ≠ j → rbar g i j = 0

  rbar_centr : ∀ g ∉ GF, ∀ i j, rbar g i j ≠ 0 → dg i + dg j = 0

  liftInvariants_finrank_eq : Module.finrank (ResidueField O) (invSub (adAct GF rbar) (gLie (ResidueField O) kind)) = rk

  rbar_Iq : ∀ q, ¬ l ∣ Nat.card ((rbar '' (Iq q : Set Gam)) : Set _)

  Rbox : TR O
  uBox : Gam → Matrix (Fin kind.n) (Fin kind.n) Rbox.C
  uBox_lift : IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar uBox
  univBox : ∀ (C : TR O) (r : Gam → Matrix (Fin kind.n) (Fin kind.n) C.C),
    IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar r →
    ∃! f : Rbox.C →ₐ[O] C.C, ∀ g, (uBox g).map f = r g

  coBox : Rbox.C →ₐ[O] TA rk Rbox.C
  coBox_counit : ∀ x, constantCoeff (coBox x) = x
  coBox_conj : ConjG GF (diagTT dg Rbox.C) (fun g => (uBox g).map MvPowerSeries.C)
    (fun g => (uBox g).map coBox)

  RV : lPl → TR O
  uV : ∀ v, Gv v → Matrix (Fin kind.n) (Fin kind.n) (RV v).C
  uV_lift : ∀ v, IsLiftG kind (GF.comap (Gv v).subtype) (chi.comp (Gv v).subtype) (fun _ => False)
    (fun g => rbar g) (uV v)
  univV : ∀ v (C : TR O) (r : Gv v → Matrix (Fin kind.n) (Fin kind.n) C.C),
    IsLiftG kind (GF.comap (Gv v).subtype) (chi.comp (Gv v).subtype) (fun _ => False)
      (fun g => rbar g) r →
    ∃! f : (RV v).C →ₐ[O] C.C, ∀ g, (uV v g).map f = r g
  coV : ∀ v, (RV v).C →ₐ[O] TA rk (RV v).C
  coV_counit : ∀ v x, constantCoeff (coV v x) = x
  coV_conj : ∀ v, ConjG (GF.comap (Gv v).subtype) (diagTT dg (RV v).C)
    (fun g => (uV v g).map MvPowerSeries.C) (fun g => (uV v g).map (coV v))

  nN : ℕ
  nN_eq : nN = kind.dimN - rk
  nx : Fin nN → Gam →₀ O
  npos : Fin nN → Fin kind.n × Fin kind.n
  ncst : Fin nN → O

  n_hom : ∀ i, (∀ g ∈ (nx i).support, g ∈ GF) ∨ (kind ≠ .GSp4 ∧ ∀ g ∈ (nx i).support, g ∉ GF)
  n_cst : ∀ i, ncst i ≠ 0 → ((∀ g ∈ (nx i).support, g ∈ GF) → dg (npos i).1 = dg (npos i).2) ∧
    ((∀ g ∈ (nx i).support, g ∉ GF) → dg (npos i).1 + dg (npos i).2 = 0)

  n_exists : ∀ (C : TR O) (r : Gam → Matrix (Fin kind.n) (Fin kind.n) C.C),
    IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar r →
    ∃ γ r', IsKerEl kind γ ∧ ConjG GF γ r r' ∧ ∀ i, nEqG (nx i) (npos i) (ncst i) r' = 0

  n_unique : ∀ (C : TR O) (r r' r'' : Gam → Matrix (Fin kind.n) (Fin kind.n) C.C) γ γ',
    IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar r →
    IsKerEl kind γ → IsKerEl kind γ' → ConjG GF γ r r' → ConjG GF γ' r r'' →
    (∀ i, nEqG (nx i) (npos i) (ncst i) r' = 0) → (∀ i, nEqG (nx i) (npos i) (ncst i) r'' = 0) →
    ∃ t : Fin rk → C.Cˣ, (∀ s, residue C.C (t s) = 1) ∧ ConjG GF (diagT dg t) r' r''

  Rl : TR O
  ιl : ∀ v, (RV v).C →ₐ[O] Rl.C
  Rl_univ : ∀ (C : TR O) (f : ∀ v, (RV v).C →ₐ[O] C.C), ∃! φ : Rl.C →ₐ[O] C.C, ∀ v, φ.comp (ιl v) = f v
  coRl : Rl.C →ₐ[O] TA rk Rl.C
  coRl_ι : ∀ v x, coRl (ιl v x) = MvPowerSeries.map (ιl v).toRingHom (coV v x)

  Rfr : TR O
  uFr : Gam → Matrix (Fin kind.n) (Fin kind.n) Rfr.C
  aFr : lPl → Matrix (Fin kind.n) (Fin kind.n) Rfr.C
  uFr_lift : IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar uFr
  aFr_ker : ∀ v, IsKerEl kind (aFr v) ∧ (kind = .GSp4 → kind.Sympl (aFr v) 1)
  univFr : ∀ (C : TR O) (r : Gam → Matrix (Fin kind.n) (Fin kind.n) C.C)
    (al : lPl → Matrix (Fin kind.n) (Fin kind.n) C.C),
    IsLiftG kind GF chi (fun g => ∃ q, g ∈ Iq q ∧ g ∈ GF ∧ rbar g = 1) rbar r →
    (∀ v, IsKerEl kind (al v) ∧ (kind = .GSp4 → kind.Sympl (al v) 1)) →
    ∃! φ : Rfr.C →ₐ[O] C.C, ∃ γ, IsKerEl kind γ ∧ ConjG GF γ (fun g => (uFr g).map φ) r ∧
      ∀ v, al v = γ * (aFr v).map φ

  frl : Rl.C →ₐ[O] Rfr.C
  frl_def : ∀ v, ConjG (GF.comap (Gv v).subtype) (aFr v)⁻¹ (fun g => uFr g)
    (fun g => (uV v g).map ((frl.comp (ιl v))))
  coFr : Rfr.C →ₐ[O] TA rk Rfr.C
  coFr_counit : ∀ x, constantCoeff (coFr x) = x
  coFr_conj : ∃ γ, IsKerEl kind γ ∧
    ConjG GF (γ * diagTT dg Rfr.C) (fun g => (uFr g).map MvPowerSeries.C) (fun g => (uFr g).map coFr) ∧
    ∀ v, (aFr v).map coFr = γ * diagTT dg Rfr.C * (aFr v).map MvPowerSeries.C * (diagTT dg Rfr.C)⁻¹
  coFr_frl : ∀ x, coFr (frl x) = MvPowerSeries.map frl.toRingHom (coRl x)
attribute [instance] LiftProb.oR LiftProb.oD LiftProb.oV LiftProb.oC LiftProb.o0 LiftProb.oF
  LiftProb.oP LiftProb.gG LiftProb.gT LiftProb.gTG LiftProb.gC LiftProb.gTD LiftProb.lF LiftProb.qF
  LiftProb.rF
end Formalism.BasicNotions.V1
namespace Formalism.MainNotions.UnusedSlot38
open Formalism.BasicNotions.V1 IsLocalRing MvPowerSeries
open scoped Classical
section Prob
variable (P : LiftProb)
def nIdeal : Ideal P.Rbox.C :=
  Ideal.span (Set.range fun i => nEqG (P.nx i) (P.npos i) (P.ncst i) P.uBox)
structure AQuot where
  Ahat : TR P.O
  q : P.Rbox.C →ₐ[P.O] Ahat.C
  surj : Function.Surjective q
  n_ker : nIdeal P ≤ RingHom.ker q
  stable : ∀ x ∈ RingHom.ker q, MvPowerSeries.map q.toRingHom (P.coBox x) = 0
end Prob
end Formalism.MainNotions.UnusedSlot38


