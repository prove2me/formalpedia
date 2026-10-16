-- Prove2me | Definitions.Def_PlatformPrecommit_Commission_Setting
-- name    : PlatformPrecommit_Commission_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:25.182223+00:00
-- url     : https://prove2.me/theorems/95014713-9465-4089-8334-91b7ff7ace4c
-- title:
--   §3 and Definition 1 — two-sided platform model, commission game, and preference ranking
-- statement:
--   Two platforms compete for consumers and independent service providers. Platform $i$ posts a consumer price $p_i$ and a provider wage $w_i$. With market size $\Omega>0$, demand competition intensity $0\leq\gamma<1$, and supply competition intensity $0\leq\beta<1$, its demand, supply, matches, and profit are
--
--   $$d_i(p)=[\Omega-p_i+\gamma p_j]^+,\quad s_i(w)=[w_i-\beta w_j]^+,\quad z_i=\min\{d_i,s_i\},\quad \pi_i=(p_i-w_i)z_i,\qquad j\ne i.$$
--
--   In mode P, each platform chooses its price and wage together. In mode C, platform $i$ first commits to a pay-out ratio $\alpha_i\in(0,1)$; after both ratios are chosen, the platforms choose prices, with wage $w_i=\alpha_i p_i$ and profit $(1-\alpha_i)p_i\min\{d_i(p),s_i(\alpha p)\}$. An SPE specifies a Nash price profile after every admissible ratio profile and rules out profitable unilateral first-stage deviations. A price equilibrium with positive profits for both platforms is selected whenever one exists.
--
--   Definition 1's ranking $C\succeq P$ means that, for each platform, the commission outcome has weakly higher price and profit and weakly lower wage and matches than the no-commitment outcome. The reverse inequalities define $P\succeq C$.
--
--   This definition layer is shared by the equilibrium and comparison statements in this mission.
--
--   **Formalization Note** Platforms are indexed by `Fin 2`. Prices and wages range over all real numbers; pay-out ratios are in $(0,1)$. The equilibrium ratio profile is symmetric when a result calls for it, but first-stage deviations may be asymmetric. The positive-profit subgame selection excludes zero-profit punishment equilibria that otherwise invalidate the paper's uniqueness claim.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), pp. 8–10, (1)–(3) and mode P; pp. 12–13, §3.4; p. 16, Definition 1

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Nash

namespace PlatformPrecommit.Commission

structure Model where
  Ω : ℝ
  β : ℝ
  γ : ℝ

def Model.Standing (M : Model) : Prop :=
  0 < M.Ω ∧ 0 ≤ M.β ∧ M.β < 1 ∧ 0 ≤ M.γ ∧ M.γ < 1

def rival (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def demand (M : Model) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  max (M.Ω - p i + M.γ * p (rival i)) 0

def supply (M : Model) (w : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  max (w i - M.β * w (rival i)) 0

abbrev PW := (Fin 2 → ℝ) × (Fin 2 → ℝ)

def matchP (M : Model) (pw : PW) (i : Fin 2) : ℝ :=
  min (demand M pw.1 i) (supply M pw.2 i)

def profP (M : Model) (pw : PW) (i : Fin 2) : ℝ :=
  (pw.1 i - pw.2 i) * matchP M pw i

def IsPNE (M : Model) (pw : PW) : Prop :=
  IsNash (fun i x => profP M x i) (fun _ => True) (fun _ _ => True)
    (fun x i (ab : ℝ × ℝ) => (Function.update x.1 i ab.1, Function.update x.2 i ab.2)) pw

def AdmissibleAlpha (α : Fin 2 → ℝ) : Prop :=
  ∀ i, 0 < α i ∧ α i < 1

def wageC (α p : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => α i * p i

def matchC (M : Model) (α p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  min (demand M p i) (supply M (wageC α p) i)

def profC (M : Model) (α p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (1 - α i) * p i * matchC M α p i

def IsCSubNE (M : Model) (α p : Fin 2 → ℝ) : Prop :=
  IsNash (fun i x => profC M α x i) (fun _ => True) (fun _ _ => True)
    (fun x i a => Function.update x i a) p

def IsSelCSubNE (M : Model) (α p : Fin 2 → ℝ) : Prop :=
  IsCSubNE M α p ∧
    ((∃ p', IsCSubNE M α p' ∧ ∀ i, 0 < profC M α p' i) →
      ∀ i, 0 < profC M α p i)

def IsCSPE (M : Model) (α : Fin 2 → ℝ) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Prop :=
  (∀ y, AdmissibleAlpha y → IsSelCSubNE M y (σ y)) ∧
  AdmissibleAlpha α ∧
  ∀ i v, 0 < v → v < 1 →
    profC M (Function.update α i v) (σ (Function.update α i v)) i ≤
      profC M α (σ α) i

def Symmetric (α : Fin 2 → ℝ) : Prop := α 0 = α 1

/-- Definition 1, specialized to C preferred to P, with comparisons for each firm. -/
def CPrefP (M : Model) : Prop :=
  ∀ α σ, IsCSPE M α σ → Symmetric α →
    ∀ pw, IsPNE M pw → (∀ i, 0 < profP M pw i) → ∀ i,
      pw.1 i ≤ (σ α) i ∧
      profP M pw i ≤ profC M α (σ α) i ∧
      wageC α (σ α) i ≤ pw.2 i ∧
      matchC M α (σ α) i ≤ matchP M pw i

/-- Definition 1, specialized to P preferred to C, with comparisons for each firm. -/
def PPrefC (M : Model) : Prop :=
  ∀ α σ, IsCSPE M α σ → Symmetric α →
    ∀ pw, IsPNE M pw → (∀ i, 0 < profP M pw i) → ∀ i,
      (σ α) i ≤ pw.1 i ∧
      profC M α (σ α) i ≤ profP M pw i ∧
      pw.2 i ≤ wageC α (σ α) i ∧
      matchP M pw i ≤ matchC M α (σ α) i

end PlatformPrecommit.Commission


