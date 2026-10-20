-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:21:29.329272+00:00
-- url     : https://prove2.me/theorems/eff247b5-d461-400c-bce5-7d80ae08d139
-- title:
--   Closure rules for computable functions
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   This module collects closure rules that let computability of composite expressions be derived automatically. The identity and constants are computable, and computable functions are closed under composition, projections and pairing.
--
--   The basic computable operations are: natural-number addition, multiplication, truncated subtraction and successor; rational addition, multiplication, negation and inverse; integer absolute value; and the rational numerator. On lists, cons, append, length and indexing with a default value are computable. So are evaluation of functions on $\{0,\dots,n-1\}$ and building the list $[f(a,0),\dots,f(a,n-1)]$ from computable components.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ComputabilityRules.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ComputabilityRules.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ComputableRules
attribute [fun_prop] Computable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] lemma identity : Computable (fun x : α => x) := Computable.id

@[fun_prop] lemma constant (b : β) : Computable (fun _ : α => b) := Computable.const b

@[fun_prop] lemma compose (f : β → γ) (g : α → β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => f (g x)) := hf.comp hg

@[fun_prop] lemma fst (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).1) := Computable.fst.comp hf

@[fun_prop] lemma snd (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).2) := Computable.snd.comp hf

@[fun_prop] lemma pair (f : α → β) (g : α → γ) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => (f x, g x)) := hf.pair hg

@[fun_prop] lemma addNat : Computable (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add.to_comp

@[fun_prop] lemma mulNat : Computable (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul.to_comp

@[fun_prop] lemma subNat : Computable (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub.to_comp

@[fun_prop] lemma succNat : Computable Nat.succ := Computable.succ

@[fun_prop] lemma constAddRat : Computable (fun p : ℚ × ℚ => p.1 + p.2) := computable_rat_add

@[fun_prop] lemma constMulRat : Computable (fun p : ℚ × ℚ => p.1 * p.2) := computable_rat_mul

@[fun_prop] lemma negRat : Computable (fun q : ℚ => -q) := computable_rat_neg

@[fun_prop] lemma invRat : Computable (fun q : ℚ => q⁻¹) := computable_rat_inv

@[fun_prop] lemma absNat : Computable Int.natAbs := primrec_int_natAbs.to_comp

@[fun_prop] lemma ratNum : Computable Rat.num := computable_rat_num

@[fun_prop] lemma consList : Computable (fun p : β × List β => p.1 :: p.2) := Primrec.list_cons.to_comp

@[fun_prop] lemma appendList : Computable (fun p : List β × List β => p.1 ++ p.2) := Primrec.list_append.to_comp

@[fun_prop] lemma lengthList : Computable (fun p : List β => p.length) := Computable.list_length

@[fun_prop] lemma getDList (b : β) : Computable (fun p : List β × ℕ => p.1.getD p.2 b) :=
  (Primrec.list_getD b).to_comp

@[fun_prop] lemma valFin {n : ℕ} : Computable (fun i : Fin n => i.val) := Primrec.fin_val.to_comp

@[fun_prop] lemma appFin {n : ℕ} : Computable (fun p : (Fin n → β) × Fin n => p.1 p.2) := Computable.fin_app

@[fun_prop] lemma ofFnList {n : ℕ} (f : α → Fin n → β) (hf : ∀ i, Computable (fun a => f a i)) :
    Computable (fun a => List.ofFn (f a)) := Computable.list_ofFn hf

end BalancedTransport.Effectivity.ComputableRules
end

end OAI


