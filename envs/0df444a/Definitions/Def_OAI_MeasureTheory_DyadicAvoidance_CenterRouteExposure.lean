-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
-- name    : OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:03:20.308986+00:00
-- url     : https://prove2.me/theorems/671d55c8-5edb-4214-ae26-5590e9b77313
-- title:
--   Centre exposure of selector tables and the first-default event
-- statement:
--   This file defines the objects used to analyse the random router at a single fixed point (the *centre*), by conditioning on all selector bits that this point reads.
--
--   **Setting.** Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$, with default child $M$; nodes are words $P$ over $\{0,\dots,M\}$ with $|P| < d$, forming the finite set $\mathcal{N}_{M,d}$, and $\varnothing$ is the root. For a choice rule $\operatorname{ch}$ assigning a child to each word $P$ and parameter $y$, the routing $R_k(P,y)$ is given by $R_0(P,y) = P$ and $R_{k+1}(P,y) = R_k(P,y)\,\operatorname{ch}(R_k(P,y),y)$ (append the chosen child). Let $\kappa_n(x) = \lfloor 2^{n+2}\{x\}\rfloor$ be the dyadic key of $x \in \mathbb{R}$, where $\{x\} = x - \lfloor x \rfloor$. Let $b : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \mathbb{N}$ be selector resolutions; a selector table $\omega$ is a $\{0,1\}$-valued function on the coordinates $((P,i),j)$ with $0 \le j < 2^{b(P,i)+2}$, and $\alpha_b(P,i,x) = ((P,i), \kappa_{b(P,i)}(x))$ is the coordinate read at $x$. Selector values are $s_\omega(P,i,x) = \omega(\alpha_b(P,i,x))$ if $|P| < d$ and $0$ otherwise, and $\operatorname{choose}(S)$ is the least $i < M$ with $S(i) = 1$, or $M$ if there is none.
--
--   1. **First default at a given stage.** For an arbitrary alphabet with a distinguished letter $\delta$ (the default), a choice rule $\operatorname{ch}$, integers $d, k$, a starting word $P$ and a parameter $y$, the event that the first default occurs at stage $k$ is
--   $$
--   k < d, \qquad \operatorname{ch}\big(R_k(P,y), y\big) = \delta, \qquad \operatorname{ch}\big(R_l(P,y), y\big) \ne \delta \ \text{ for all } l < k.
--   $$
--
--   2. **Centre exposure.** For a centre $x \in \mathbb{R}$, the exposure of a selector table $\omega$ is the array of all selector bits read at $x$:
--   $$
--   E_x(\omega)(P,i) = \omega\big(\alpha_b(P,i,x)\big), \qquad (P,i) \in \mathcal{N}_{M,d} \times \{0,\dots,M-1\}.
--   $$
--
--   3. **Canonical completion.** For an arbitrary array $\xi : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \{0,1\}$, the completion $\omega^{\xi}$ is the selector table with $\omega^{\xi}(\alpha_b(P,i,x)) = \xi(P,i)$ for all $(P,i)$ and $\omega^{\xi} = 0$ at every coordinate not of this form. It is well defined because $(P,i) \mapsto \alpha_b(P,i,x)$ is injective, and the file proves $E_x(\omega^{\xi}) = \xi$. The completion is merely a deterministic representative of the fibre $\{\omega : E_x(\omega) = \xi\}$, not a probability law.
--
--   4. **Centre choice.** The first-success choice made by a table $\omega$ at a word $P$, read at the centre $x$, is $c_x(P,\omega) = \operatorname{choose}\big(i \mapsto s_\omega(P,i,x)\big)$.
--
--   5. **Good exposures.** An array $\xi$ is *good* at $x$ if the centre route of its completion reaches the default child before depth $d$:
--   $$
--   \exists\, k < d : \qquad c_x\big(R_k(\varnothing, \omega^{\xi}),\ \omega^{\xi}\big) = M,
--   $$
--   where the route is computed with the choice rule $(P,\omega) \mapsto c_x(P,\omega)$, the table playing the role of the parameter.
--
--   The exposure partitions the selector tables into atoms $\{\omega : E_x(\omega) = \xi\}$. Since the centre choices at nodes of depth below $d$ read only exposed bits, an array $\xi$ is good exactly when every table in its atom meets a default on its centre route before depth $d$. These notions are used to split the failure probability at a fixed centre according to the exposed bits.
--
--   **Formalization Note** The first-default event `FirstDefaultAt` is stated for arbitrary types of children and parameters. The completion is `Function.extend` of $\xi$ along the coordinate map with junk value `false`, and the default child in `GoodExposure` is `Fin.last M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterRouteExposure.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterRouteExposure.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_ι u_X u_Y

noncomputable section

namespace Problem310.CenterRouteExposure
open Problem310.RoutingPath

/-- The event that the first default occurs at a specified stage. -/
def FirstDefaultAt {ι : Type u_ι} {X : Type u_X} (choose : List ι → X → ι)
    (default : ι) (d k : ℕ) (P : List ι) (x : X) : Prop :=
  k < d ∧ choose (routeFrom choose k P x) x = default ∧
    ∀ l < k, choose (routeFrom choose l P x) x ≠ default

open Problem310.FiniteTableModel Problem310.OrderedRouting

/-- The full deterministic center exposure: one bit for every selector table. -/
def centerExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ω : SelectorTable b) : Node M d × Fin M → Bool :=
  fun e => ω (selectorAddress b e.1 e.2 x)

/-- Complete any exposure assignment by setting all unexposed bits to false.
This is only a deterministic representative of an atom, not a probability law. -/
def centerCompletion {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : SelectorTable b :=
  Function.extend (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x)
    ξ (fun _ => false)

@[simp] theorem centerExposure_completion {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    centerExposure b x (centerCompletion b x ξ) = ξ := by
  funext e
  exact (center_selectorAddress_injective b x).extend_apply ξ (fun _ => false) e

/-- The actual first-success choice made by a selector table at a fixed center. -/
def centerChoice {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (P : List (Child M)) (ω : SelectorTable b) : Child M :=
  chooseChild (fun i => selectorValue b ω P i x)

/-- The good atoms are those whose (equivalently, every) center route has a default. -/
def GoodExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : Prop :=
  ∃ k < d, centerChoice b x
    (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
      (centerCompletion b x ξ) = Fin.last M

end Problem310.CenterRouteExposure

end

end OAI


