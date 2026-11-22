-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:08:21.086301+00:00
-- url     : https://prove2.me/theorems/dbfbf489-356f-4ac6-ab28-2ac3408e6c20
-- title:
--   Rho WApply
-- statement:
--   Definitions and structural lemmas for Rho WApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RhoWApply.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
section Act
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)
def mvPt (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : pts S :=
  open Classical in if h : ∃ y', actR g y y' then h.choose else y
def actRule (g : G) (f : Rules pts) : Rules pts := fun p y => f p (mvPt pts actR g y)
def actL (g : G) : Rules pts →ₗ[K] Rules pts where
  toFun := actRule pts actR g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def ActTotal : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y : pts S), ∃ y', actR g y y'
def ActFun : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR g y y'' → mapR (AlgHom.id K S) y' y''
def ActOne : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (y : pts S), actR 1 y y
def ActMul : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR h y' y'' → actR (g * h) y y''
def ActNat : Prop :=
  ∀ (g : G) (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
    (y y' : pts S) (z z' : pts T), mapR φ y z → actR g y y' → actR g z z' → mapR φ y' z'
def ActBor : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' z z' : pts S),
    borR t y z → actR g y y' → actR g z z' → borR t y' z'
variable {pts actR}
theorem mvPt_spec (hT : ActTotal pts actR) (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    actR g y (mvPt pts actR g y) := by
  have h := hT g S y
  unfold mvPt
  rw [dif_pos h]
  exact h.choose_spec
variable (pts actR)
theorem actL_mem [Fintype ι] (hT : ActTotal pts actR) (hN : ActNat pts mapR actR) (hB : ActBor pts borR actR)
    (e : ι → ℕ) (g : G) {f : Rules pts} (hf : f ∈ secW pts mapR borR e) :
    actL pts actR g f ∈ secW pts mapR borR e := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact h1 p q φ _ _ (hN g p.R q.R φ y (mvPt pts actR g y) z (mvPt pts actR g z) hyz
      (mvPt_spec hT g y) (mvPt_spec hT g z))
  · intro p t y y' hyy
    exact h2 p t _ _ (hB g p.R t y (mvPt pts actR g y) y' (mvPt pts actR g y') hyy
      (mvPt_spec hT g y) (mvPt_spec hT g y'))
theorem actL_one (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hO : ActOne pts actR)
    {f : Rules pts} (hf : IsNatural pts mapR f) : actL pts actR 1 f = f := by
  funext p y
  show f p (mvPt pts actR 1 y) = f p y
  exact hf p p (AlgHom.id K p.R) y _ (hF 1 p.R y y _ (hO p.R y) (mvPt_spec hT 1 y))
theorem actL_mul (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hM : ActMul pts actR)
    (g h : G) {f : Rules pts} (hf : IsNatural pts mapR f) :
    actL pts actR (g * h) f = actL pts actR g (actL pts actR h f) := by
  funext p y
  show f p (mvPt pts actR (g * h) y) = f p (mvPt pts actR h (mvPt pts actR g y))
  have h1 : actR (g * h) y (mvPt pts actR h (mvPt pts actR g y)) :=
    hM g h p.R y _ _ (mvPt_spec hT g y) (mvPt_spec hT h _)
  exact (hf p p (AlgHom.id K p.R) _ _ (hF (g * h) p.R y _ _ (mvPt_spec hT (g * h) y) h1)).symm
structure ActLaws : Prop where
  total : ActTotal pts actR
  func : ActFun pts mapR actR
  one : ActOne pts actR
  mul : ActMul pts actR
  nat : ActNat pts mapR actR
  bor : ActBor pts borR actR
variable {pts mapR borR actR}
def rhoW [Fintype ι] (hL : ActLaws pts mapR borR actR) (e : ι → ℕ) :
    G →* Module.End K (secW pts mapR borR e) where
  toFun g :=
    { toFun := fun f => ⟨actL pts actR g f, actL_mem pts mapR borR actR hL.total hL.nat hL.bor e g f.2⟩
      map_add' := fun f f' => Subtype.ext (map_add (actL pts actR g) f.1 f'.1)
      map_smul' := fun c f => Subtype.ext (map_smul (actL pts actR g) c f.1) }
  map_one' := by
    ext f : 1
    exact Subtype.ext (actL_one pts mapR actR hL.total hL.func hL.one f.2.1)
  map_mul' g h := by
    ext f : 1
    exact Subtype.ext (actL_mul pts mapR actR hL.total hL.func hL.mul g h f.2.1)
def RhoStabW [Fintype ι] (hL : ActLaws pts mapR borR actR) (e : ι → ℕ) (W : Submodule K (secW pts mapR borR e)) :
    Prop :=
  ∀ (g : G) (f : secW pts mapR borR e), f ∈ W → rhoW hL e g f ∈ W
def chiDet {D L : Type} [CommGroup D] [Monoid L] (det : G →* D) (χ : D →* Lˣ) : G →* Lˣ := χ.comp det
end Act
end Formalism.L2.Pj


