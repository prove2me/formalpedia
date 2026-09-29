-- Prove2me | Definitions.Def_CerednikDrinfeld_CartierLMapFibre
-- name    : CerednikDrinfeld_CartierLMapFibre
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c3d81eb5-7182-5bcf-a4a9-dfbb16a616a0
-- title:
--   Pi-operator, N(M), critical indices, and L-maps
-- statement:
--   Throughout, $p$ is a prime, $B$ a commutative ring (of characteristic $p$ where Verschiebung is involved), $X$ a `FormalODModule p B` with underlying formal group law `X.F`, $M =$ `CartierModule p X.F` its Cartier module, and $j\colon \mathbb{Z}_{p^2} \to B$ a ring homomorphism. `piOp` is the additive endomorphism $\Pi$ of $M$ obtained by functoriality from the endomorphism `X.varpiEnd` of `X.F`; `piOp_apply` identifies it with the action `CartierModule.endAct X.varpiEnd`, and `piOp_comp_verschiebung` records $\Pi V = V\Pi$ in characteristic $p$. On top of the abstract constructions of `CartierN` applied to the pair $(V,\Pi)$ one gets: `NMod`, the quotient of $M \times M$ by the image of $m \mapsto (Vm, -\Pi m)$; `lambdaN`, the induced additive map sending the class of $(m,m')$ to $\Pi m + V m'$; and `NPiece j n`, the image in `NMod` of $M_n \times M_n$, where $M_n =$ `X.gradedPiece j n` consists of those $f$ with $\mathrm{endAct}\,(X.\mathrm{actEnd}(\tau(c)))\,f = \mathrm{homothety}\,(j(\tau(c))^{p^n})\,f$ for all $c$ in $\mathbb{F}_{p^2}$, $\tau$ the Teichmüller lift. Two characterisations are recorded: `CritChart.IsCritical X j n` holds exactly when $\Pi f \in V M$ for every $f \in M_n$, and `CritChart.invariants X j n` consists of the $m \in M_n$ with $\Pi m = V m$.
--
--   `IsPiBijective X j n` is the conjunction of: for $f \in M_n$, $\Pi f \in VM$ implies $f \in VM$; and every $h \in M_{n+1}$ is of the form $\Pi f + Vg$ with $f \in M_n$ and $g \in M$. `IsLMap X j L`, for an additive map $L\colon M \to$ `NMod`, is a structure whose four fields are the assertions that $\lambda \circ L$ is the Frobenius of $M$; that $L(Vx)$ is the class of $(\Pi x, 0)$; that $L(M_n) \subseteq$ `NPiece j n` for every $n$; and that if $n$ is critical, $f \in M_n$ and $Vg = \Pi f$, then $L(f)$ is the class of $(g,0)$. For such an $L$ the module provides $\varphi$, the endomorphism of `NMod` sending the class of $(m,m')$ to $L(m) +$ the class of $(m',0)$; $\eta$, its fixed subgroup; and $u\colon \eta \to M/VM$, the restriction of the map taking the class of $(m,m')$ to $m \bmod VM$.
--
--   **Relation to Mathlib.** Mathlib has no Cartier theory of formal group laws and no analogue of the modules $N(M)$; these are the project's own notions, phrased in terms of Mathlib's additive quotient groups and `AddMonoidHom` API.
--
--   **Where it is used.** These are the characteristic-$p$ ingredients of the Boutot–Carayol analysis of special formal $\mathcal{O}_D$-modules (the $\Pi$-operator on the Cartier module, the module $N(M)$ with its graded pieces, the critical/$\Pi$-bijective dichotomy for indices, and the map $L_M$ together with $\varphi_M$, $\eta_M$ and $u_M$), which underlie the Čerednik–Drinfel'd uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CartierLMapFibre.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev piOp (X : FormalODModule p B) : CartierModule p X.F →+ CartierModule p X.F :=
  CartierModule.map X.varpiEnd

theorem piOp_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp f = CartierModule.endAct X.varpiEnd f := rfl

theorem piOp_comp_verschiebung [CharP B p] (X : FormalODModule p B) :
    X.piOp.comp CartierModule.verschiebung = CartierModule.verschiebung.comp X.piOp :=
  AddMonoidHom.ext fun f => CartierModule.map_verschiebung X.varpiEnd f

abbrev NMod [CharP B p] (X : FormalODModule p B) : Type u :=
  CartierN.NMod (CartierModule.verschiebung (p := p) (Φ := X.F)) X.piOp

abbrev lambdaN [CharP B p] (X : FormalODModule p B) : X.NMod →+ CartierModule p X.F :=
  CartierN.lambda CartierModule.verschiebung X.piOp X.piOp_comp_verschiebung

abbrev NPiece [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : AddSubgroup X.NMod :=
  CartierN.piece CartierModule.verschiebung X.piOp (X.gradedPiece j n) (X.gradedPiece j n)

theorem critChart_isCritical_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    CritChart.IsCritical X j n ↔
      ∀ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F, X.piOp f = CartierModule.verschiebung g :=
  forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem mem_critChart_invariants_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ CritChart.invariants X j n ↔ m ∈ X.gradedPiece j n ∧ X.piOp m = CartierModule.verschiebung m :=
  Iff.rfl

def IsPiBijective [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : Prop :=
  (∀ f ∈ X.gradedPiece j n, (∃ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f) →
      ∃ g : CartierModule p X.F, CartierModule.verschiebung g = f) ∧
    ∀ h ∈ X.gradedPiece j (n + 1), ∃ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
      h = X.piOp f + CartierModule.verschiebung g

structure IsLMap [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (L : CartierModule p X.F →+ X.NMod) : Prop where

  lambdaN_comp : X.lambdaN.comp L = CartierModule.frobenius

  comp_verschiebung :
    L.comp CartierModule.verschiebung = (CartierN.inl CartierModule.verschiebung X.piOp).comp X.piOp

  mem_nPiece : ∀ (n : ℕ), ∀ f ∈ X.gradedPiece j n, L f ∈ X.NPiece j n

  eq_inl_of_isCritical : ∀ (n : ℕ), CritChart.IsCritical X j n → ∀ f ∈ X.gradedPiece j n,
    ∀ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f →
      L f = CartierN.inl CartierModule.verschiebung X.piOp g

namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}

abbrev phi (h : X.IsLMap j L) : X.NMod →+ X.NMod :=
  CartierN.phi CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev eta (h : X.IsLMap j L) : AddSubgroup X.NMod :=
  CartierN.eta CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev u (h : X.IsLMap j L) :
    h.eta →+ CartierModule p X.F ⧸ (CartierModule.verschiebung (p := p) (Φ := X.F)).range :=
  CartierN.u CartierModule.verschiebung X.piOp L h.comp_verschiebung

end IsLMap

end FormalODModule

end CerednikDrinfeld

end


