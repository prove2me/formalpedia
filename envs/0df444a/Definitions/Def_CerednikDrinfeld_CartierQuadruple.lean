-- Prove2me | Definitions.Def_CerednikDrinfeld_CartierQuadruple
-- name    : CerednikDrinfeld_CartierQuadruple
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/972f894b-07da-5bd0-83d2-62d2df73032e
-- title:
--   Drinfeld quadruple attached to a rigidified special formal module
-- statement:
--   Throughout, $p$ is a prime, $O$ a commutative ring, $\Phi$ a `FormalODModule p (O ⧸ pIdeal p O)`, and $B$ a commutative ring. For a formal $\mathcal{O}_D$-module $X$ over $B$, `lieVarpi` is the $B$-linear endomorphism of the tangent module `X.Lie` given by multiplication by the matrix of linear parts of the power-series system `X.varpi`. For a ring map $g\colon B\to S$ the abbreviations `XS`, `XbarS`, `PhibarS` name the base changes of `t.X` along $g$, of `t.Xbar` along the induced map $B/p\to S/p$, and of $\Phi$ along $O/p\to B/p\to S/p$; `jS`, `jSbar`, `jPhiS` are the corresponding structure maps $\mathbb{Z}_{p^2}\to S$, resp. $\to S/p$, and `IsGradedS`, `IsGradedSbar`, `IsGradedPhiS` assert that the degree-$0$ and degree-$1$ graded pieces of the relevant Cartier module are complementary. The additive maps `redC` (reduction mod $p$), `bcPhi` (base change of $\Phi$) and `rhoC` (functoriality along $t.\rho$) on Cartier modules are shown to commute with the integral Verschiebung and with the $\varpi$-action, so they induce maps `etaRed` on the associated $N$-modules and, composed with a fixed additive rigidification $r_\Phi\colon\mathbb{Z}_p^2\to N(M_\Phi)$, the map `rigidNum`$\colon\mathbb{Z}_p^2\to N(M_{\overline X_S})$. `LatticeRel E n r \bar z v` says there are $m,k\in\mathbb{N}$ and $w\in\mathbb{Z}_p^2$ with $p^m v=w$ in $\mathbb{Q}_p^2$ and $p^k r(w)=p^{k+n+m}\bar z$ in `E.NMod`: a cleared-denominator form of $p^{-n}r(v)=\bar z$. For a canonical $L$-map $L$ on the graded data of $X_S$, `IsEtaSection … i z v` says $z$ lies in the $i$-th piece `etaPiece L … i` and `LatticeRel` holds for the reduction of $\varpi^i z$ against $p^i v$ with shift `t.n`; `isEtaSection_zero_iff` and `isEtaSection_one_iff` spell out the cases $i=0,1$.
--
--   `IsCartierQuadruple ι hcΦ rΦ ψ t Q` is a relation between a rigidified object $t$ over a $\mathbb{Z}_p$-algebra $B$ and a `DrinfeldDatum` $Q$ over $B$ for $(\mathbb{Z}_p,\mathbb{Q}_p,p)$. It requires: $t.\rho$ is a homomorphism of formal $\mathcal{O}_D$-modules from $\Phi$ base-changed along the residue map of $\psi$ to `t.Xbar`; $B$-linear isomorphisms $\tau_0\colon Q.T_0\cong$ `lieZero`, $\tau_1\colon Q.T_1\cong$ `lieOne` carrying $Q.\Pi_0,Q.\Pi_1$ to `lieVarpi`; and, at every prime $x$ of $B$, that $v\in N_0(x)$ (resp. $N_1(x)$) holds exactly when some $f\notin x$, gradedness data over the localisation $B_f$, canonical $L$ and $z$ make `IsEtaSection … 0 z v` (resp. $\dots 1\,z\,v$) true, together with a germwise comparison: for each such datum there are $m$ in the Cartier module over $B_f$, $s\in Q.T_0$ (resp. $Q.T_1$) and $b\notin x$ such that $m$ modulo the image of Verschiebung equals the image `u L … z`, the element $Q.u_0(1\otimes v)$ (resp. $Q.u_1$) is the germ $s/b$, and $\tau_0 s$ (resp. $\tau_1 s$) equals $b$ times the image of `tangent m` coordinatewise in $B_x$. The lattices and stalk maps are thus pinned down on basic open sets $D(f)$, with no commutation of $\eta$ with localisation presupposed. `Bloc`, `locHom`, `Baway`, `awayHom`, `awayToLoc` provide these localisations and the comparison $B_f\to B_x$ for $f\notin x$. Finally, `drinfeldQuadruple` chooses, from the hypothesis that some $Q$ is in the relation, one such datum, and `drinfeldQuadruple_spec` records that the chosen datum satisfies `IsCartierQuadruple`; no existence or uniqueness is asserted here.
--
--   **Relation to Mathlib.** Formal $\mathcal{O}_D$-modules, their Cartier modules and Drinfeld data are the project's own notions; the ambient localisation machinery used (`Localization.AtPrime`, `Localization` at powers of an element, `IsLocalization.Away.lift`, `LocalizedModule`, `PrimeSpectrum`) is Mathlib's.
--
--   **Where it is used.** These definitions belong to the Čerednik–Drinfeld part of the development: they encode the passage from a rigidified special formal $\mathcal{O}_D$-module over a base $B$ to a Drinfeld datum (lattice pair, invertible modules with $\Pi$, and stalk maps) on $\operatorname{Spec} B$, which is what the $p$-adic uniformisation of Shimura curves is built from in the project's route to the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CartierQuadruple.lean

import Mathlib
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace CerednikDrinfeld

namespace FormalODModule

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

def lieVarpi (X : FormalODModule p B) : X.Lie →ₗ[B] X.Lie :=
  Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi)

end FormalODModule

namespace SpecialFormal

namespace Rigidified

open FormalODModule FormalOmega MvFormalGroup MvFormalGroup.CartierModule GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

abbrev jbar (ι : Zp2 p →+* O) : Zp2 p →+* O ⧸ pIdeal p O :=
  (Ideal.Quotient.mk (pIdeal p O)).comp ι

variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

section Over

variable {S : Type} [CommRing S]

abbrev XS (t : Rigidified p Φ B) (g : B →+* S) : FormalODModule p S := t.X.map g

abbrev XbarS (t : Rigidified p Φ B) (g : B →+* S) : FormalODModule p (S ⧸ pIdeal p S) :=
  t.Xbar.map (reduceMap g)

abbrev PhibarS (ψ : O →+* B) (g : B →+* S) : FormalODModule p (S ⧸ pIdeal p S) :=
  (Φ.map (residueMap ψ)).map (reduceMap g)

theorem XS_F_map_mk (t : Rigidified p Φ B) (g : B →+* S) :
    (t.XS g).F.map (Ideal.Quotient.mk (pIdeal p S)) = (t.XbarS g).F := by
  show (t.X.F.map g).map (Ideal.Quotient.mk (pIdeal p S)) =
    (t.X.F.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap g)
  rw [map_map_ringHom, map_map_ringHom]
  congr 1

abbrev redC (t : Rigidified p Φ B) (g : B →+* S) :
    CartierModule p (t.XS g).F →+ CartierModule p (t.XbarS g).F :=
  baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) (t.XS_F_map_mk g)

abbrev bcPhi (ψ : O →+* B) (g : B →+* S) :
    CartierModule p Φ.F →+ CartierModule p (PhibarS (Φ := Φ) ψ g).F :=
  (baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)).comp
    (baseChange (Φ := Φ.F) (residueMap ψ))

abbrev rhoC (ψ : O →+* B) (t : Rigidified p Φ B)
    (hρ : IsLawHom (Φ.map (residueMap ψ)).F t.Xbar.F t.ρ) (g : B →+* S) :
    CartierModule p (PhibarS (Φ := Φ) ψ g).F →+ CartierModule p (t.XbarS g).F :=
  CartierModule.map
    ((hρ.map (reduceMap g)).toHom : MvFormalGroup.Hom (PhibarS (Φ := Φ) ψ g).F (t.XbarS g).F)

theorem redC_verschiebungInt (t : Rigidified p Φ B) (g : B →+* S)
    (m : CartierModule p (t.XS g).F) :
    t.redC g (verschiebungInt m) = verschiebungInt (t.redC g m) :=
  baseChangeEq_verschiebungInt _ _ m

theorem redC_endAct_varpiEnd (t : Rigidified p Φ B) (g : B →+* S)
    (m : CartierModule p (t.XS g).F) :
    t.redC g (endAct (t.XS g).varpiEnd m) = endAct (t.XbarS g).varpiEnd (t.redC g m) :=
  baseChangeEq_endAct _ _ (fun _ => rfl) m

theorem bcPhi_verschiebungInt (ψ : O →+* B) (g : B →+* S) (m : CartierModule p Φ.F) :
    bcPhi (Φ := Φ) ψ g (verschiebungInt m) = verschiebungInt (bcPhi (Φ := Φ) ψ g m) := by
  show baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)
      (baseChange (Φ := Φ.F) (residueMap ψ) (verschiebungInt m)) =
    verschiebungInt (baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)
      (baseChange (Φ := Φ.F) (residueMap ψ) m))
  rw [baseChangeEq_verschiebungInt (residueMap ψ) rfl m]
  exact baseChangeEq_verschiebungInt _ rfl _

theorem bcPhi_endAct_varpiEnd (ψ : O →+* B) (g : B →+* S) (m : CartierModule p Φ.F) :
    bcPhi (Φ := Φ) ψ g (endAct Φ.varpiEnd m) =
      endAct (PhibarS (Φ := Φ) ψ g).varpiEnd (bcPhi (Φ := Φ) ψ g m) := by
  show baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)
      (baseChange (Φ := Φ.F) (residueMap ψ) (endAct Φ.varpiEnd m)) =
    endAct (PhibarS (Φ := Φ) ψ g).varpiEnd
      (baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)
        (baseChange (Φ := Φ.F) (residueMap ψ) m))
  rw [baseChangeEq_endAct (ψ := (Φ.map (residueMap ψ)).varpiEnd) (residueMap ψ) rfl
    (fun _ => rfl) m]
  exact baseChangeEq_endAct (ψ := (PhibarS (Φ := Φ) ψ g).varpiEnd) _ rfl (fun _ => rfl) _

theorem rhoC_verschiebungInt (ψ : O →+* B) (t : Rigidified p Φ B)
    (hρ : IsLawHom (Φ.map (residueMap ψ)).F t.Xbar.F t.ρ) (g : B →+* S)
    (m : CartierModule p (PhibarS (Φ := Φ) ψ g).F) :
    rhoC ψ t hρ g (verschiebungInt m) = verschiebungInt (rhoC ψ t hρ g m) :=
  map_verschiebungInt _ m

theorem rhoC_endAct_varpiEnd (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (m : CartierModule p (PhibarS (Φ := Φ) ψ g).F) :
    rhoC ψ t hOD.1 g (endAct (PhibarS (Φ := Φ) ψ g).varpiEnd m) =
      endAct (t.XbarS g).varpiEnd (rhoC ψ t hOD.1 g m) := by
  show CartierModule.map _ (CartierModule.map _ m) = CartierModule.map _ (CartierModule.map _ m)
  rw [← MvFormalGroup.CartierModule.map_comp, ← MvFormalGroup.CartierModule.map_comp]
  congr 2
  apply MvFormalGroup.Hom.ext
  show (t.ρ.map (reduceMap g)).comp (((Φ.map (residueMap ψ)).varpi).map (reduceMap g)) =
    ((t.Xbar.varpi).map (reduceMap g)).comp (t.ρ.map (reduceMap g))
  rw [← Series.map_comp _ _ _ (Φ.map (residueMap ψ)).isLawHom_varpi.1,
    ← Series.map_comp _ _ _ hOD.1.1, hOD.2.2]

abbrev jS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S :=
  g.comp (structureMap ι ψ)

abbrev jSbar (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S ⧸ pIdeal p S :=
  (reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp (structureMap ι ψ))

abbrev jPhiS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S ⧸ pIdeal p S :=
  (reduceMap g).comp ((residueMap ψ).comp (jbar ι))

abbrev IsGradedS (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) (g : B →+* S) : Prop :=
  IsCompl ((t.XS g).gradedPiece (jS ι ψ g) 0) ((t.XS g).gradedPiece (jS ι ψ g) 1)

abbrev IsGradedSbar (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) (g : B →+* S) :
    Prop :=
  IsCompl ((t.XbarS g).gradedPiece (jSbar ι ψ g) 0) ((t.XbarS g).gradedPiece (jSbar ι ψ g) 1)

abbrev IsGradedPhiS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Prop :=
  IsCompl ((PhibarS (Φ := Φ) ψ g).gradedPiece (jPhiS ι ψ g) 0)
    ((PhibarS (Φ := Φ) ψ g).gradedPiece (jPhiS ι ψ g) 1)

def etaRed (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) :
    ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod →+
      ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb).NMod :=
  ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).nMap
    ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb)
    (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g)

def rigidNum (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod) (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g) :
    (Fin 2 → ℤ_[p]) →+ ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb).NMod :=
  (((PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (jPhiS ι ψ g) hcΦg).nMap
      ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb)
      (rhoC ψ t hOD.1 g) (rhoC_verschiebungInt ψ t hOD.1 g) (rhoC_endAct_varpiEnd ψ t hOD g)).comp
    (((Φ.toGradedCartierModuleData (jbar ι) hcΦ).nMap
        ((PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (jPhiS ι ψ g) hcΦg)
        (bcPhi (Φ := Φ) ψ g) (bcPhi_verschiebungInt (Φ := Φ) ψ g)
        (bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)).comp rΦ)

def LatticeRel {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'} (E : GradedCartierModuleData p S' jS')
    (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (zbar : E.NMod) (v : Fin 2 → ℚ_[p]) : Prop :=
  ∃ (m k : ℕ) (w : Fin 2 → ℤ_[p]),
    (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
      p ^ k • r w = p ^ (k + n + m) • zbar

def IsEtaSection (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod) (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).IsCanonicalLMap L)
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (v : Fin 2 → ℚ_[p]) : Prop :=
  let D := (t.XS g).toGradedCartierModuleData (jS ι ψ g) hc
  z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i ∧
    LatticeRel ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb) t.n
      (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg)
      (t.etaRed ι ψ g hc hcb (((D.nVarpi : D.NMod →ₗ[WittVector p S] D.NMod) ^ (i : ℕ)) z))
      ((p : ℚ_[p]) ^ (i : ℕ) • v)

theorem isEtaSection_zero_iff (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod) (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).IsCanonicalLMap L)
    (z : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p]) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL 0 z v ↔
      z ∈ ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 ∧
        LatticeRel ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb) t.n
          (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg) (t.etaRed ι ψ g hc hcb z) v := by
  simp only [IsEtaSection, Fin.val_zero, pow_zero, one_smul, Module.End.one_apply]

theorem isEtaSection_one_iff (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod) (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).IsCanonicalLMap L)
    (z : ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p]) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL 1 z v ↔
      z ∈ ((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).etaPiece L
          hL.isCartierLMap.map_verschiebung 1 ∧
        LatticeRel ((t.XbarS g).toGradedCartierModuleData (jSbar ι ψ g) hcb) t.n
          (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg)
          (t.etaRed ι ψ g hc hcb (((t.XS g).toGradedCartierModuleData (jS ι ψ g) hc).nVarpi z))
          ((p : ℚ_[p]) • v) := by
  simp only [IsEtaSection, Fin.val_one, pow_one]

end Over

abbrev Bloc (x : PrimeSpectrum B) : Type := Localization.AtPrime x.asIdeal

abbrev locHom (x : PrimeSpectrum B) : B →+* Bloc x := algebraMap B (Bloc x)

abbrev Baway (f : B) : Type := Localization (Submonoid.powers f)

abbrev awayHom (f : B) : B →+* Baway f := algebraMap B (Baway f)

def awayToLoc (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) : Baway f →+* Bloc x :=
  IsLocalization.Away.lift f
    (g := locHom x) (IsLocalization.map_units (Bloc x) (⟨f, hf⟩ : x.asIdeal.primeCompl))

def IsCartierQuadruple (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=

  IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧
  ∃ (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))),

    (∀ s : Q.T₀, ((τ₁ (Q.Pi₀ s) : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie)) ∧
    (∀ s : Q.T₁, ((τ₀ (Q.Pi₁ s) : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie)) ∧

    ∀ (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (x : PrimeSpectrum B),

      (∀ v, v ∈ Q.N₀ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v) ∧

      (∀ v, v ∈ Q.N₁ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₀)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₀ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₀ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i)) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₁)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₁ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₁ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i))

def drinfeldQuadruple (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B :=
  h.choose

theorem drinfeldQuadruple_spec (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    t.IsCartierQuadruple ι hcΦ rΦ ψ (t.drinfeldQuadruple ι hcΦ rΦ ψ h) :=
  h.choose_spec

end Rigidified

end SpecialFormal

end CerednikDrinfeld

end


