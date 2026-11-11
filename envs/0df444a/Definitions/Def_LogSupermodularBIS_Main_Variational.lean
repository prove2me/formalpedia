-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Variational
-- name    : LogSupermodularBIS_Main_Variational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:48.133566+00:00
-- url     : https://prove2.me/theorems/1d993d7c-e856-4a4c-93e7-72522c9ad86f
-- title:
--   Branching rules, guides, the exact guide, the Lovász extension and the variational objective
-- statement:
--   A **branching rule** $\theta$ assigns $\theta_v\in[0,1]$ to every internal node $v$ (prefix of length $<d$). The descent with rule $\theta$ reaches the prefix $x\in\{0,1\}^j$ with probability
--   $$\nu_\theta(x)=\prod_{i\le j:\,x_i=1}\theta_{x_{<i}}\prod_{i\le j:\,x_i=0}(1-\theta_{x_{<i}}),\tag{3.1}$$
--   and $\nu_\theta$ also denotes the induced leaf law. The **tree objective** is the bracket of (3.4), $\sum_v\nu_\theta(v)H(\theta_v)+E_{\nu_\theta}\Phi$, the sum over internal nodes, with $H(p)=-p\log p-(1-p)\log(1-p)$ the binary entropy and $0\log0=0$. The entropy of a finite law is $H(\nu)=-\sum_x\nu(x)\log\nu(x)$.
--
--   The logit is $a(u)=\log(u/(1-u))$. The inputs $U=(U_1,\dots,U_d)$ are independent uniform on $(0,1)$. The **threshold descent** of $\theta$ is $f^\theta_i(U)=\mathbf 1\{U_i\ge1-\theta_{f^\theta_{<i}(U)}\}$, and the **exact guide** of $\mu=e^\Phi/Z_\Phi$ is $f=f^p$, with $p$ the conditional marginal probabilities (3.7).
--
--   A **guide** (Definition 3.5) is a measurable map $F:(0,1)^d\to[0,1]^d$ whose $i$th row depends only on $U_1,\dots,U_i$; it is **Boolean** if its values lie in $\{0,1\}^d$. Its linear score is $\sum_iE[a(U_i)F_i(U)]$.
--
--   The **Lovász extension** (3.12) is defined on all of $\mathbb R^d$: order $z_{j_1}\ge\dots\ge z_{j_d}$, put $S_t=\{j_1,\dots,j_t\}$, $S_0=\emptyset$, and
--   $$\Phi^L(z)=\sum_{t=1}^dz_{j_t}\bigl(\Phi(S_t)-\Phi(S_{t-1})\bigr).$$
--   The **variational objective** (3.13) of a guide is
--   $$\mathcal P(F)=\sum_{i=1}^dE[a(U_i)F_i(U)]+E\,\Phi^L(F(U)).$$
--
--   **Formalization Note.** A branching rule is a function on all lists of Booleans; only its values at internal nodes matter. A guide is given on all of $\mathbb R^d$, and only its values on $(0,1)^d$ are constrained. Ties in the sort are broken by a fixed rule (`Tuple.sort`); the value of $\Phi^L$ does not depend on it.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 12–18 (PDF 13–19), §3, (3.1), (3.4), (3.7), Definition 3.5, (3.12), (3.13)

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Weight

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# The variational principle on the self-reduction tree (§3, pp. 12–18)

`Φ : (Fin d → Bool) → ℝ` is a potential, normalized by `Φ 0 = 0` where needed. A branching rule
`θ : List Bool → ℝ` gives a number `θ v ∈ [0,1]` at every internal node `v` (prefix of length
`< d`); values elsewhere are irrelevant. Inputs `U = (U_1, …, U_d)` are independent uniform on
`(0,1)`; coordinate `i : Fin d` is the paper's `U_{i+1}`.
-/

/-- The internal nodes: prefixes of length `< d`, listed as `List.ofFn y`, `y : Fin j → Bool`. -/
def IsBranchingRule (d : ℕ) (θ : List Bool → ℝ) : Prop :=
  ∀ v : List Bool, v.length < d → θ v ∈ Set.Icc (0 : ℝ) 1

/-- The probability (3.1) that the descent with rule `θ` reaches the node `v`: the product of the
branching probabilities along the path. -/
noncomputable def reachProb (θ : List Bool → ℝ) (v : List Bool) : ℝ :=
  ∏ k : Fin v.length, if v[k] then θ (v.take k) else 1 - θ (v.take k)

/-- The induced law `ν_θ` on the leaves. -/
noncomputable def leafLaw {d : ℕ} (θ : List Bool → ℝ) (x : Fin d → Bool) : ℝ :=
  reachProb θ (List.ofFn x)

/-- The entropy `H(ν) = −Σ ν(x) log ν(x)` of a finite law (with `0 log 0 = 0`). -/
noncomputable def lawEntropy {α : Type*} [Fintype α] (ν : α → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (ν x)

/-- The bracket of (3.4): `Σ_v ν_θ(v) H(θ_v) + E_{ν_θ} Φ`, the first sum over the internal nodes
`v` (prefixes of length `j < d`), `H` the binary entropy. -/
noncomputable def treeObjective {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (θ : List Bool → ℝ) : ℝ :=
  (∑ j : Fin d, ∑ y : Fin j.val → Bool,
      reachProb θ (List.ofFn y) * Real.binEntropy (θ (List.ofFn y))) +
    ∑ x, leafLaw θ x * Φ x

/-- The conditional marginal probabilities `p` of `μ = e^Φ / Z_Φ`, as a branching rule. -/
noncomputable def condMarginalRule {d : ℕ} (Φ : (Fin d → Bool) → ℝ) : List Bool → ℝ :=
  condMarginal Φ

/-- The logit `a(u) = log(u / (1 − u))`. -/
noncomputable def logit (u : ℝ) : ℝ := Real.log (u / (1 - u))

/-- The open unit cube `(0,1)^d`. -/
def openCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1

/-- The law of `U = (U_1, …, U_d)`: independent uniform inputs on `(0,1)`. -/
noncomputable def unifCube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)

/-- The prefix `f^θ_{<i}(U)` reached by the threshold descent (3.7) of `θ` after `i` steps. -/
noncomputable def descentPrefix {d : ℕ} (θ : List Bool → ℝ) (U : Fin d → ℝ) : ℕ → List Bool
  | 0 => []
  | i + 1 =>
      let v := descentPrefix θ U i
      if h : i < d then v ++ [decide (1 - θ v ≤ U ⟨i, h⟩)] else v

/-- The threshold descent `f^θ_i(U) = 1{U_i ≥ 1 − θ_{f^θ_{<i}(U)}}` (3.7). -/
noncomputable def thresholdDescent {d : ℕ} (θ : List Bool → ℝ) (U : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if 1 - θ (descentPrefix θ U i.val) ≤ U i then 1 else 0

/-- The exact guide `f = f^p` of `μ = e^Φ / Z_Φ`. -/
noncomputable def exactGuide {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (U : Fin d → ℝ) : Fin d → ℝ :=
  thresholdDescent (condMarginalRule Φ) U

/-- Definition 3.5: a guide is a measurable map `F : (0,1)^d → [0,1]^d` whose `i`th row depends
only on `U_1, …, U_i`. (It is given on all of `ℝ^d`; only its values on `(0,1)^d` matter.) -/
def IsGuide (d : ℕ) (F : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  Measurable F ∧
  (∀ u ∈ openCube d, ∀ i, F u i ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ u ∈ openCube d, ∀ u' ∈ openCube d, ∀ i : Fin d,
      (∀ j : Fin d, j ≤ i → u j = u' j) → F u i = F u' i)

/-- A Boolean guide: a guide with values in `{0,1}^d`. -/
def IsBooleanGuide (d : ℕ) (F : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  IsGuide d F ∧ ∀ u ∈ openCube d, ∀ i, F u i = 0 ∨ F u i = 1

/-- The set of guides on `d` inputs. -/
def guides (d : ℕ) : Set ((Fin d → ℝ) → Fin d → ℝ) := {F | IsGuide d F}

/-- The Boolean vector of a `{0,1}`-valued real vector (`true` iff the value is `1`). -/
noncomputable def toConfig {d : ℕ} (z : Fin d → ℝ) : Fin d → Bool := fun i => decide (z i = 1)

/-- The linear score `Σ_i E[a(U_i) F_i(U)]` of a guide. -/
noncomputable def linearScore {d : ℕ} (F : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∫ u, logit (u i) * F u i ∂unifCube d

/-- The left side of (3.8) for a Boolean guide: `Σ_i E[a(U_i) F_i(U)] + E Φ(F(U))`. -/
noncomputable def booleanObjective {d : ℕ} (Φ : (Fin d → Bool) → ℝ)
    (F : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  linearScore F + ∫ u, Φ (toConfig (F u)) ∂unifCube d

/-- The Lovász extension (3.12) on all of `ℝ^d`: sort `z_{j_1} ≥ ⋯ ≥ z_{j_d}` (ties broken by a
fixed rule), put `S_t = {j_1, …, j_t}` and `Φ^L(z) = Σ_t z_{j_t} (Φ(S_t) − Φ(S_{t−1}))`. The
order `σ = Tuple.sort (−z)` lists the coordinates by decreasing value of `z`. -/
noncomputable def lovaszExt {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (z : Fin d → ℝ) : ℝ :=
  let σ := Tuple.sort (fun i => -z i)
  let S : ℕ → Fin d → Bool := fun t j => decide ((σ.symm j).val < t)
  ∑ t : Fin d, z (σ t) * (Φ (S (t.val + 1)) - Φ (S t.val))

/-- The variational objective (3.13): `P(F) = Σ_i E[a(U_i) F_i(U)] + E Φ^L(F(U))`. -/
noncomputable def variationalObjective {d : ℕ} (Φ : (Fin d → Bool) → ℝ)
    (F : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  linearScore F + ∫ u, lovaszExt Φ (F u) ∂unifCube d

end LogSupermodularBIS.Main


