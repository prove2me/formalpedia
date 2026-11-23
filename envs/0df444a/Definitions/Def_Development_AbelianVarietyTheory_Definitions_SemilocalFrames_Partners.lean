-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Partners
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Partners
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:36.477292+00:00
-- url     : https://prove2.me/theorems/54f87f34-e8f2-485e-bc01-a626fed0e20b
-- title:
--   Partners
-- statement:
--   Definitions and structural lemmas for Partners, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/Partners.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc Matrix
namespace GlobalTheory.SgDen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def ct (L : LocE F E) {m n : Type} (X : Matrix m n E) : Matrix n m E := (X.map L.cj)ᵀ
def IntO (L : LocE F E) {m n : Type} (X : Matrix m n E) : Prop := ∀ a b, X a b ∈ L.O
def InP (L : LocE F E) (j : ℕ) (y : E) : Prop :=
  ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∃ x ∈ L.O, y = algebraMap F E ((ϖ : F) ^ j) * x
def Unimod (L : LocE F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ct L J = J ∧ IntO L J ∧ ∃ u ∈ L.O, J.det * u = 1
def Prim (L : LocE F E) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι E) : Prop :=
  IntO L X ∧ ∃ P : Matrix ι (Fin n) E, IntO L P ∧ P * X = 1
def gram (L : LocE F E) {n : ℕ} {ι : Type} (J : Matrix (Fin n) (Fin n) E)
    (X : Matrix (Fin n) ι E) : Matrix ι ι E := ct L X * J * X
def AutO (L : LocE F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {k | IntO L k ∧ ct L k * J * k = J}
def resQ (F : Type) [Field F] [ValuativeRel F] : ℕ := Nat.card 𝓀[F]
open scoped Classical in

def eta (E : Type) [CommRing E] : ℝ := if IsField E then -1 else 1
def corank (L : LocE F E) {ι : Type} [Fintype ι] (T : Matrix ι ι E) : ℕ :=
  sInf {c | ∃ G : Matrix ι (Fin c) E, IntO L G ∧ ∀ v : ι → E, (∀ a, v a ∈ L.O) →
    ∃ (u : ι → E) (w : Fin c → E), (∀ a, u a ∈ L.O) ∧ (∀ a, w a ∈ L.O) ∧
      ∀ a, InP L 1 ((v - T *ᵥ u - G *ᵥ w) a)}
def densF (q : ℕ) (η : ℝ) (n a c : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (n + 1 - a - c) n, (1 - (η * (q : ℝ)⁻¹) ^ i)
def volM [MeasurableSpace E] (ν : Measure E) (n : ℕ) (ι : Type) [Fintype ι] :
    Measure (Fin n → ι → E) := Measure.pi fun _ => Measure.pi fun _ => ν
def densJ [MeasurableSpace E] (L : LocE F E) (ν : Measure E) {n : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] (J : Matrix (Fin n) (Fin n) E) (T : Matrix ι ι E) (j : ℕ) : ℝ :=
  (volM ν n ι {X | Prim L (Matrix.of X) ∧
      ∀ a b, InP L j ((gram L J (Matrix.of X) - T) a b)}).toReal *
    (resQ F : ℝ) ^ (j * Fintype.card ι ^ 2)
def herm (L : LocE F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  (fun i => L.cj (y i)) ⬝ᵥ (J *ᵥ x)
def SelfDual (L : LocE F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, herm L J v w ∈ L.O
def IsFrame (L : LocE F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : F)
    (f : Fin (r + 1) → Fin n → E) : Prop :=
  ∀ a b, herm L J (f b) (f a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0
def zhat (L : LocE F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f f' : Fin (r + 1) → Fin n → E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => herm L J (f' b) (f a)
def Xsp {n r : ℕ} (f : Fin (r + 1) → Fin n → E) : Submodule E (Fin n → E) :=
  Submodule.span E (Set.range fun a : Fin r => f a.castSucc)
def W0 (L : LocE F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f f' : Fin (r + 1) → Fin n → E) : Set (Fin n → E) :=
  {w | ∀ a, herm L J w (f a) = 0 ∧ herm L J w (f' a) = 0}
def kap {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := Z⁻¹ (Fin.last r) (Fin.last r)
def omP (L : LocE F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f f' : Fin (r + 1) → Fin n → E) : Fin n → E :=
  ∑ b, (zhat L J f f')⁻¹ b (Fin.last r) • f' b
def om (L : LocE F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f f' : Fin (r + 1) → Fin n → E) : Fin n → E :=
  ∑ a, (ct L (zhat L J f f'))⁻¹ a (Fin.last r) • f a
def RegZ (L : LocE F E) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  IsUnit Z.det ∧ IsUnit (1 - algebraMap F E (T * T') * (kap Z * L.cj (kap Z)))
variable [MeasurableSpace E]
def levInv (M : Model F E) : E :=
  match M.split with
  | none => 1
  | some g => algebraMap F E (g.q : F)⁻¹
def TOK (M : Model F E) (T T' : F) : Prop :=
  match M.split with
  | none => True
  | some g => T ∈ 𝒪[F] ∧ T⁻¹ ∈ 𝒪[F] ∧ T ≠ 0 ∧ (T - T') / (g.q : F) ∈ 𝒪[F]
def mvec (M : Model F E) {n r : ℕ} (f f' : Fin (r + 1) → Fin n → E) :
    Fin (r + 1) ⊕ Fin (r + 1) → Fin n → E
  | Sum.inl a => f a
  | Sum.inr b =>
    match M.split with
    | none => f' b
    | some _ => levInv M • (f' b - f b)
def Generic (M : Model F E) {n r : ℕ} (Λ : Submodule M.L.O (Fin n → E))
    (f f' : Fin (r + 1) → Fin n → E) : Prop :=
  (∀ i, mvec M f f' i ∈ Λ) ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range (mvec M f f')) →
    v ∈ Submodule.span M.L.O (Set.range (mvec M f f'))
def gramM (M : Model F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f f' : Fin (r + 1) → Fin n → E) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  Matrix.of fun i j => herm M.L J (mvec M f f' j) (mvec M f f' i)
def datum (M : Model F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule M.L.O (Fin n → E)) (f f' : Fin (r + 1) → Fin n → E) :
    Set (((Fin n → E) × E × E) × ((Fin n → E) × E × E)) :=
  {p | p.1.1 ∈ W0 M.L J f f' ∧ p.2.1 ∈ W0 M.L J f f' ∧ ∃ x ∈ Xsp f, ∃ x' ∈ Xsp f',
    p.1.1 + p.1.2.1 • f (Fin.last r) + p.1.2.2 • omP M.L J f f' + x ∈ Λ ∧
    p.2.1 + p.2.2.1 • f' (Fin.last r) + p.2.2.2 • om M.L J f f' + x' ∈ Λ ∧
    levInv M • ((p.1.1 + p.1.2.1 • f (Fin.last r) + p.1.2.2 • omP M.L J f f' + x) -
      (p.2.1 + p.2.2.1 • f' (Fin.last r) + p.2.2.2 • om M.L J f f' + x')) ∈ Λ}
def tau0 (M : Model F E) (T T' : F) : E :=
  match M.split with
  | none => 0
  | some g => g.e.symm (-T / (g.q : F), T' / (g.q : F))
def zz (M : Model F E) {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) : Matrix (Fin m) (Fin m) E :=
  match M.split with
  | none => Z
  | some g => Matrix.of fun a b =>
      g.e.symm ((g.e (Z a b)).1 / (g.q : F), -(g.e (Z b a)).2 / (g.q : F))
def zzp (M : Model F E) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  zz M Z - Matrix.single (Fin.last r) (Fin.last r) (tau0 M T T')
def IntR (M : Model F E) {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) : Prop := ∀ a b, Z a b ∈ M.R
abbrev Mod (M : Model F E) {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Type :=
  (Fin (r + 1) → M.R) ⧸
    Submodule.span M.R {v : Fin (r + 1) → M.R | ∃ j : Fin r, ∀ a, (v a : E) = Z a j.castSucc}
def IsoTh (M : Model F E) {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Type :=
  {φ : Mod M Z ≃ₗ[M.R] Mod M Z' //
    φ (Submodule.Quotient.mk (Pi.single (Fin.last r) 1)) =
      Submodule.Quotient.mk (Pi.single (Fin.last r) 1) ∧
    ∀ v v' : Fin (r + 1) → M.R, (∀ a, (v a : E) = Z a (Fin.last r)) →
      (∀ a, (v' a : E) = Z' a (Fin.last r)) →
        φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v'}
open scoped Classical in

def nTh (M : Model F E) {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℕ :=
  if IntR M Z ∧ IntR M Z' then Nat.card (IsoTh M Z Z') else 0
def Partners (M : Model F E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule M.L.O (Fin n → E)) (f f₁ f₂ : Fin (r + 1) → Fin n → E) :
    Set (Submodule M.L.O (Fin n → E)) :=
  {Λ₂ | SelfDual M.L J Λ₂ ∧ Generic M Λ₂ f f₂ ∧ datum M J Λ₂ f f₂ = datum M J Λ f f₁}
def Ktop (M : Model F E) {r : ℕ} (τ : E) (w w' : Pt E (r + 1)) : ℂ :=
  ∫ p : GlobalTheory.SgLoc.Orb w × GlobalTheory.SgLoc.Orb w',
    GlobalTheory.SgLoc.phase M w p.1 * conj (GlobalTheory.SgLoc.phase M w' p.2) *
      (nTh M (GlobalTheory.SgLoc.orbMat w p.1 - Matrix.single (Fin.last r) (Fin.last r) τ)
        (GlobalTheory.SgLoc.orbMat w' p.2 - Matrix.single (Fin.last r) (Fin.last r) τ) : ℂ)
    ∂((GlobalTheory.SgLoc.orbMeas M w).prod (GlobalTheory.SgLoc.orbMeas M w'))
def dPh (M : Model F E) (τ : E) (t : Eˣ) (s : ℕ+) : ℂ :=
  if (s : ℕ) = 2 then M.psiR (τ * ((t⁻¹ : Eˣ) : E)) else 1
end GlobalTheory.SgDen


