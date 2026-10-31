-- Prove2me | Definitions.Def_FoucaudIdentification_DiameterTwo_Solutions
-- name    : FoucaudIdentification_DiameterTwo_Solutions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T02:20:22.982235+00:00
-- url     : https://prove2.me/theorems/402daeb6-85df-4b9a-8d6a-4dd4dd3029b2
-- title:
--   Definitions 1–3 — locating-dominating sets, identifying codes and open codes
-- statement:
--   The three problems use vertex subsets. LD requires closed domination and distinguishes every pair outside the selected set; selecting an endpoint counts as separation of its pair. ID requires closed domination and distinct closed-neighborhood traces for all distinct vertices. OLD requires open domination and distinct open-neighborhood traces for all distinct vertices. The minimum cardinality is an extended natural, with infinity for infeasibility. Twin-free and open twin-free mean distinct closed and open neighborhoods respectively, including their vacuous empty and singleton cases.
-- source:
--   Foucaud et al., arXiv:1405.2424v3, pp. 1–2, Definitions 1–3. https://arxiv.org/abs/1405.2424v3

import Definitions.Def_FoucaudIdentification_DiameterTwo_Neighborhoods

namespace FoucaudIdentification.DiameterTwo

/-- The three source solution notions; no feasibility or nonemptiness is assumed. -/
inductive Problem where
  | LD | ID | OLD
  deriving DecidableEq

def Problem.dom {V : Type} (p : Problem) (G : SimpleGraph V) : V → V → Prop :=
  match p with
  | .OLD => G.Adj
  | _ => ClosedDom G

def Problem.sep {V : Type} (p : Problem) (G : SimpleGraph V) (x u v : V) : Prop :=
  match p with
  | .LD => x = u ∨ x = v ∨ Distinguishes (ClosedDom G) x u v
  | .ID => Distinguishes (ClosedDom G) x u v
  | .OLD => Distinguishes G.Adj x u v

def Solution {V : Type} (p : Problem) (G : SimpleGraph V) (S : Finset V) : Prop :=
  DominatesOn (p.dom G) S Set.univ ∧ SeparatesOn (p.sep G) S Set.univ

/-- The minimum, with infinity for an infeasible graph. -/
noncomputable def optimum {V : Type} (p : Problem) (G : SimpleGraph V) : ℕ∞ :=
  sInf {k | ∃ S : Finset V, Solution p G S ∧ k = (S.card : ℕ∞)}

def TwinFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v, (∀ x, ClosedDom G x u ↔ ClosedDom G x v) → u = v

def OpenTwinFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v, (∀ x, G.Adj x u ↔ G.Adj x v) → u = v

end FoucaudIdentification.DiameterTwo


