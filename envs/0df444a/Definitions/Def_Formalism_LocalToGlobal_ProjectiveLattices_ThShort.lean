-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ThShort
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:00:57.022828+00:00
-- url     : https://prove2.me/theorems/18dd3fef-d313-4405-b413-23dadc48ce43
-- title:
--   Th Short
-- statement:
--   Definitions and structural lemmas for Th Short, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial
attribute [local instance] Over.cartesianMonoidalCategory
section UU
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)
def IsUUOver (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ s₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U₁ U₂ : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₁ U₁ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₁ s₁ s₂ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₂ U₂ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₂ s₂ F
end UU
section Lat
variable (E : Type) [Field E] [NumberField E]
def stdLat (n : ℕ) : Submodule (𝓞 E) (Fin n → E) := Submodule.pi Set.univ fun _ => 1
structure GenLat (n : ℕ) where

  La : Submodule (𝓞 E) (Fin n → E)
variable {E} {n : ℕ}
def GenLat.Ln (Λ : GenLat E n) : Submodule (𝓞 E) (Fin n → E) := Λ.La ⊓ stdLat E n
def GenLat.TrivAt (Λ : GenLat E n) (bad : ℕ) : Prop :=
  ∃ k : ℕ, Nat.Coprime k bad ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La
def GenLat.LevOK (Λ : GenLat E n) (N M : ℕ) : Prop :=
  Odd N ∧ M ∣ N ∧ Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.Ln
def GenLat.Unimod [IsCMField E] (Λ : GenLat E n) : Prop :=
  ∀ v : Fin n → E, v ∈ Λ.La ↔
    ∀ w ∈ Λ.La, ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range
def detSet (M : Submodule (𝓞 E) (Fin n → E)) : Set E :=
  {d | ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ M) ∧ d = Matrix.det (Matrix.of fun i j => v j i)}
def GenLat.mIdx (Λ : GenLat E n) (N r : ℕ) : ℕ :=
  ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.Ln.toAddSubgroup).index ^ r
def GenLat.zCard (Λ : GenLat E n) (N r : ℕ) : ℕ :=
  ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r
end Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def idealAt {n : ℕ} (M : Submodule (𝓞 E) (Fin n → E)) (τ : E →+* ℂ) : Submodule (𝓞 c.F) c.F :=
  Submodule.span (𝓞 c.F) (embF c τ '' detSet M)
def BetaIs {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  Submodule.span (𝓞 c.F) {β} * ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ =
    ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ
def BetaAbs {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  ∀ σ : c.F →+* ℂ, ‖σ β‖ ^ 2 =
    ((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q)
open Classical in

def betaH {n : ℕ} (Λ : GenLat E n) : c.F :=
  if h : ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β then h.choose else 1
def InZh {n : ℕ} (Λ : GenLat E n) (N : ℕ) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  (∀ b, a b ^ (N ^ 2) = 1) ∧
  ∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
    ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
      ∀ i, (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j)).prod = 1
def Mfr (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)
open Classical in

def cSep (l : Level H) : 𝓞 E := if h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb then h.choose else 0
def pairL {n : ℕ} (x0 x : Fin n → Dw.La) : ℤ := ∑ b, Dw.EF (x0 b) (cSep l • x b)
def zetaM : c.F := (⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / l.M)
abbrev LevQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)
def levRep (q : LevQ Dw l) : Dw.La := Classical.choose (Submodule.Quotient.mk_surjective _ q)
def AdmX {n : ℕ} (rk : Bool) (x0 : Fin n → Dw.La) : Prop :=
  Submodule.span (𝓞 E) (x0 '' {b | rk = true ∨ b.val < Dw.p + Dw.q}) ⊔
    (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) = ⊤
def x0Dat {n : ℕ} (x0 : Fin n → Dw.La) : (Fin n → LevQ Dw l) → c.F :=
  fun q => zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))
structure DeltaDat (n : ℕ) : Type 1 where

  pd : ℕ

  I : Ideal (𝓞 E)

  l₂ : Level H

  Xo₂ : Moduli Dw l₂

  c₂ : Coeff l₂

  hF : c₂.F = c.F

  r : Xo₂.X ⟶ Xo.X

  m : SABMap Xo₂.univ.t Xo.univ.t r

  nab₂ : NabV Xo₂ c₂

  cδ : Rul Xo₂ c₂

  φδ : (Fin n → LevQ Dw l₂) → c.F
variable {Xo c} in

def DeltaDat.eF {n : ℕ} (d : DeltaDat Xo c n) : c.F ≃ₐ[ℚ] d.c₂.F := IntermediateField.equivOfEq d.hF.symm
variable {Xo c} in

def DeltaDat.w {n : ℕ} (d : DeltaDat Xo c n) (x0 : Fin n → Dw.La) : (Fin n → LevQ Dw d.l₂) → d.c₂.F :=
  fun q => d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q)
def SecMaps {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (a : LB.Sec A) (b : LB.Sec B) : Prop :=
  ∀ p : B.ι × A.ι, (X.presheaf.map (homOfLE (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ B.U p.1)).op).hom (b.f p.1) =
    ((@id (Γ(X, B.U p.1 ⊓ A.U p.2)ˣ) (w.s p) : Γ(X, B.U p.1 ⊓ A.U p.2)ˣ) : Γ(X, B.U p.1 ⊓ A.U p.2)) *
      (X.presheaf.map (homOfLE (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ A.U p.2)).op).hom (a.f p.2)
variable {Xo c} in

def DeltaDat.EtaOK {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  (∀ a, (d.Xo₂.univ.eta a ^ d.pd).left ≫ d.m.φ = d.r ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (d.Xo₂.univ.etaA a ^ (d.l₂.A / l.A)).left ≫ d.m.φ = d.r ≫ (Xo.univ.etaA a).left
variable {Xo c} in

def FrOver {n : ℕ} (d : DeltaDat Xo c n) {k : Type} [CommRing k]
    [Algebra c.F k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k) : Prop :=
  y₂.x ≫ d.r = y.x ∧ (∀ τ i, y₂.u τ i ≫ d.m.φ = y.u τ i) ∧
  ∃ (w₀ : LB.Iso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ)) (pm : Gx y₂.x ⟶ Gx y.x)
    (t : LB.Sec (LB.LinComb (Xo.univ.t.PP.L.pull d.m.φ) (K := Fin 1)
      (fun _ => (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (fun _ => 1))),
    w₀.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec d.Xo₂.univ.t.G) (fun _ => 1))
      d.Xo₂.univ.t.PP.rig (d.m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ d.m.φ ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left ∧
    SecMaps (LB.linCombIso w₀ (K := Fin 1) (fun _ => (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (fun _ => 1))
      y₂.s t ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
      (h : (LB.LinComb (Xo.univ.t.PP.L.pull d.m.φ) (K := Fin 1)
        (fun _ => (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (fun _ => 1)).U (fun _ _ => i 0) ≤
          pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (y.s.f i) = t.f (fun _ _ => i 0)
variable {Xo c} in

def DeltaDat.IsLev {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  l.Dvd d.l₂ ∧ d.l₂.M = l.M * d.pd ∧ Nat.Coprime d.pd l.M ∧ d.l₂.Mb = l.Mb * d.I ∧
    d.I ⊔ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
    d.EtaOK ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
        ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y) ∧
    d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ≠ 0)
open Classical in

def cHalf (H : Host E) (I : Ideal (𝓞 E)) : 𝓞 E :=
  if h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I then h.choose else 0
def qRep {K : Submodule (𝓞 E) Dw.La} (q : Dw.La ⧸ K) : Dw.La := Classical.choose (Submodule.Quotient.mk_surjective _ q)
abbrev LaJ {n : ℕ} (d : DeltaDat Xo c n) : Type := Dw.La ⧸ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)
abbrev LaI {n : ℕ} (d : DeltaDat Xo c n) : Type := Dw.La ⧸ (d.I • ⊤ : Submodule (𝓞 E) Dw.La)
variable {Xo c} in

def DeltaDat.PhiPin {n : ℕ} (d : DeltaDat Xo c n) (ph : (Fin n → LaJ Xo c d) → c.F)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d) : Prop :=
  (∀ x x' : Fin n → LaJ Xo c d, (∀ b : Fin n, b.val < Dw.p + Dw.q → x b = x' b) → ph x = ph x') ∧
  (∀ x, ph x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤) ∧
  (∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d),
    (∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
      Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v))))) →
    ∀ x, ph (fun b => kst (x b)) = (((ψ k)⁻¹ : c.Fˣ) : c.F) * ph x) ∧
  ph x₀ = 1 ∧ Submodule.span (𝓞 E) (x₀ '' {b | b.val < Dw.p + Dw.q}) = ⊤ ∧
  ∀ q : Fin n → LevQ Dw d.l₂, d.eF (d.φδ q) =
    ∑ᶠ x : Fin n → LaJ Xo c d, d.eF (ph x) *
      ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))
variable {Xo c} in

def DeltaDat.PsiTie {n : ℕ} (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (g : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X),
    g.InGam l d.l₂ → (∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a)) → d.Xo₂.LevAut g ρ →
    (∀ a : Dw.La, (Submodule.Quotient.mk (g.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra d.c₂.F K] (y y' : FrPt d.Xo₂ d.c₂ K),
      y'.x = y.x ≫ ρ.hom →
      evR d.Xo₂ d.c₂ d.cδ y' = algebraMap d.c₂.F K (d.eF ((ψ k : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
def letB {n : ℕ} (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) : MvPolynomial (LtN Dw n) c.F :=
  ∑ j, C (embF c σ (b j)) * X (⟨σ, i, j⟩ : LtN Dw n)
def symO {n : ℕ} (Λ : GenLat E n) : Subring (MvPolynomial (LtN Dw n) c.F) :=
  Subring.closure ((Set.range fun o : integralClosure ℤ c.F => C (o : c.F)) ∪
    {f | ∃ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E), b ∈ Λ.La ∧ f = letB c σ i b})
def harmL {n : ℕ} (Λ : GenLat E n) (a : (E →+* ℂ) × ℕ → ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  {P | P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧
    P ∈ symO c Λ}
def GeoInj {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {n : ℕ} {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (k : Type) [Field k] (ψ : S →+* k) (g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0), g.left = spMap ψ →
    Function.Injective fun i b => g ≫ z i b
def ShortValAt (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧
    (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧
    (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧
    (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) ∧
    φ v = algebraMap c.F S' (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S' (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) *
          ∏ b, nab y' ((N : ℤ) ^ 2) (F q i b) (colOf m b)
def IsShortRule {n : ℕ} (dδ : DeltaDat Xo c n) (Λ : GenLat E n) (N : ℕ)
    (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ v : k, ShortValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (dδ.w x0) Λ (dδ.eF (betaH (Dw := Dw) c Λ)) N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) P) y₂ v ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ * v
def shortGen (_nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (dδ : DeltaDat Xo c n) :
    Set (Rul Xo c) :=
  {f | f ∈ sec Xo c a n ∧ ∃ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt dδ.l₂.M ∧ Λ.LevOK N dδ.l₂.M ∧
    AdmX (l := l) (decide (n = nV)) x0 ∧ P ∈ harmL c Λ a ∧ IsShortRule Xo c dδ Λ N x0 P f}
def KPsiIn : Prop :=
  ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : c.F, β ≠ 0 ∧
    Submodule.span (𝓞 c.F) {β} =
      ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ∧
    ∀ σ : c.F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)
def BetaExists (n bad : ℕ) : Prop :=
  KPsiIn (Dw := Dw) c → ∀ Λ : GenLat E n, Λ.Unimod → Λ.TrivAt bad →
    ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β
def ShortValTot (_nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (dδ : DeltaDat Xo c n) : Prop :=
  ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    Λ.Unimod → Λ.TrivAt bad → Λ.TrivAt dδ.l₂.M → Λ.LevOK N dδ.l₂.M →
    AdmX (l := l) (decide (n = nV)) x0 → P ∈ harmL c Λ a →
      (∀ (S : Type) [CommRing S] [Algebra dδ.c₂.F S] (y₂ : FrPt dδ.Xo₂ dδ.c₂ S),
        ∃! v, ShortValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (dδ.w x0) Λ (dδ.eF (betaH (Dw := Dw) c Λ)) N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) P) y₂ v) ∧
      ∃ f ∈ sec Xo c a n, IsShortRule Xo c dδ Λ N x0 P f
def ShortInCusp (nab : NabV Xo c) (bad nV : ℕ) (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (dδ : DeltaDat Xo c n) : Prop :=
  Dom a n → LastPos Dw a → shortGen Xo c nab bad nV a n dδ ⊆ cusp a n
def noDelta (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (n : ℕ) : DeltaDat Xo c n where
  pd := 1
  I := ⊤
  l₂ := l
  Xo₂ := Xo
  c₂ := c
  hF := rfl
  r := 𝟙 _
  m := m
  nab₂ := nab
  cδ := 1
  φδ := fun _ => 1
def ShortThetaUnit (nab : NabV Xo c) (n : ℕ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) N l.M → P ∈ harmA c a n → ∃ u : (𝓞 c.F)ˣ,
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (w : (Fin n → LevQ Dw l) → S),
      ShortValAt Xo c nab (x0Dat c x0) ⟨stdLat E n⟩ (betaH (Dw := Dw) c ⟨stdLat E n⟩) N P y v →
      (∀ q, ThValAt Xo c nab y (fun b => levRep (q b)) P (w q)) →
      v = algebraMap c.F S ((u : 𝓞 c.F) : c.F) * algebraMap c.F S ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (zetaM c ^ pairL (l := l) x0 fun b => levRep (q b)) * w q
def SpanningAtDominantWeight (nab : NabV Xo c) (bad nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (dδ : ∀ n, DeltaDat Xo c n) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n →
      (cusp a n : Set (Rul Xo c)) ⊆ Submodule.span c.F (shortGen Xo c nab bad nV a n (dδ n))
def ShortNe0 (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n → cusp a n ≠ ⊥ →
      ∃ f ∈ shortGen Xo c nab bad nV a n (dδ n), f ≠ 0
def CMP {n : ℕ} (d : DeltaDat Xo c n) (σ0 : d.c₂.F →+* ℂ) (Cls : Type) [CommGroup Cls] (δ : Cls →* d.c₂.Fˣ)
    (gdet : FrPt d.Xo₂ d.c₂ (CAt σ0) → Cls) (inv : Bool) : Prop :=
  d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 ∧ ∀ y : FrPt d.Xo₂ d.c₂ (CAt σ0),
    evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt σ0) ((if inv then (δ (gdet y))⁻¹ else δ (gdet y) : d.c₂.Fˣ) : d.c₂.F)
end Formalism.L2.Pj


