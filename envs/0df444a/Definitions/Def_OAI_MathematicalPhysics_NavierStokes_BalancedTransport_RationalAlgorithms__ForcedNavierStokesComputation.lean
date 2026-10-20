-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:58:12.786511+00:00
-- url     : https://prove2.me/theorems/63f0380a-ff49-46d9-b5d2-200f75fb3b13
-- title:
--   Computable case distinctions and rational inverses
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   This module adds three computability facts. A definition by cases, $a\mapsto$ ($f(a)$ if $p(a)$, else $g(a)$), is computable when $f$, $g$ and the decision procedure for $p$ are computable. The integer sign function is primitive recursive. The rational inverse $q\mapsto q^{-1}$, with $0^{-1}=0$, is computable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_ite {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  exact (Computable.cond hp hf hg).of_eq (fun a => by
    by_cases h : p a <;> simp [h])

lemma primrec_int_sign : Primrec Int.sign := by
  have h : Primrec (fun n : ℕ => if n = 0 then (0 : ℤ) else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  refine (primrec_int_cases Primrec.id (h.comp Primrec.snd).to₂
    (Primrec.const (-1 : ℤ)).to₂).of_eq ?_
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

lemma computable_rat_inv : Computable (fun q : ℚ => q⁻¹) := by
  have hn : Computable (fun q : ℚ => q.num.sign * (q.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (primrec_int_sign.to_comp.comp computable_rat_num)
      (primrec_int_ofNat.to_comp.comp computable_rat_den)
  have hnum : Computable (fun q : ℚ => q⁻¹.num) := hn.of_eq (fun q => (Rat.num_inv q).symm)
  have hd : Computable (fun q : ℚ => q⁻¹.den) := by
    refine (computable_ite (Primrec.eq.decide.to_comp.comp computable_rat_num (Computable.const 0))
      (Computable.const 1) (primrec_int_natAbs.to_comp.comp computable_rat_num)).of_eq ?_
    intro q
    exact (Rat.den_inv q).symm
  exact (computable_rat_of_parts hnum hd (fun q => q⁻¹.den_ne_zero)).of_eq
    (fun q => Rat.num_div_den q⁻¹)

end BalancedTransport.Effectivity
end

end OAI


