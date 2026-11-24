-- Prove2me | Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy
-- name    : InterpOptStop_SAA_Supplement_GridPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:45:58.201802+00:00
-- url     : https://prove2.me/theorems/863e7018-852d-4556-b02b-f126f48778bb
-- title:
--   Cube partition, survival-conditioned grid policy and intermediate policies
-- statement:
--   For a positive integer $m$, partition each coordinate into $[0,1/m]$ and $(j/m,(j+1)/m]$, $1\le j<m$. Products give the $m^n$ cells. Thus shared faces have a unique owner, including both cube endpoints. Let $A_t$ mean survival before period $t$ under the already constructed policy. The approximating policy is defined forward by
--   $$\hat\pi(t,x)=\mathrm{stop}\quad\Longleftrightarrow\quad E[g(t,x(t))\mid A_t,x(t)\in h(x)]>\beta E[C_t^*(x(t))\mid A_t,x(t)\in h(x)].$$
--   At $t=1$ the survival condition is empty. Conditional means on null events are zero, and ties select go. The intermediate policy $\tilde\pi^i$ follows $\hat\pi$ for the first $i$ periods and the Bellman policy thereafter, for every $i=0,\ldots,T$. Hence its endpoints are the optimal Bellman policy and $\hat\pi$. For depth bounds use the nonnegative level count $k=\lceil\log_2\max\{1,2TL\lambda\sqrt n/\epsilon\}\rceil$, which is zero when the coefficient is zero. This explicitly corrects the negative signed depth possible in the printed all-$\epsilon$ formula; see DISPROOF.md and the theorem's disclosure.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, (EC.32)–(EC.34), pp. ec24–ec25; intermediate policies, p. ec25; Theorem EC.2 proof, p. ec29

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_CubeBellman

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

/-- Faces go to the lower cell. In particular 0 belongs to cell 0, and 1 to cell m-1. -/
noncomputable def cell {n : ℕ} (m : ℕ) (x : Cube n) : Fin n → ℕ :=
  fun i => ⌈(m : ℝ) * x.val i⌉₊ - 1

def InCell {n m : ℕ} (h : Fin n → Fin m) (x : Cube n) : Prop :=
  cell m x = fun i => (h i).val

/-- Conditional mean on an event. Probability-zero events give zero. -/
noncomputable def eventMean {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) (f : α → ℝ) : ℝ :=
  (∫ x in A, f x ∂μ) / (μ A).toReal

/-- The conditioning event uses ALL preceding computed actions and the current cube. -/
def gridEvent {n T : ℕ} (m : ℕ) (q : List (Cube n → Act)) (k : Fin T) (x : Cube n) :
    Set (Fin T → Cube n) :=
  {p | (∀ j : Fin T, j.val < k.val → (q.getD j.val (fun _ => Act.go)) (p j) = Act.go) ∧
    cell m (p k) = cell m x}

/-- Construct stages forward, so the survival event depends only on earlier actions.
The final T-entry list is exactly (EC.32)--(EC.34); ties and null cubes get go. -/
noncomputable def gridPrefix {n T : ℕ} (μ : Measure (Fin T → Cube n)) (β : ℝ)
    (g : Fin T → Cube n → ℝ) (K : Fin T → Kernel (Cube n) (Cube n)) (m : ℕ) :
    ℕ → List (Cube n → Act)
  | 0 => []
  | r + 1 =>
    let q := gridPrefix μ β g K m r
    q ++ [fun x => if hk : r < T then
      let k : Fin T := ⟨r, hk⟩
      if eventMean μ (gridEvent m q k x) (fun p => g k (p k)) >
          β * eventMean μ (gridEvent m q k x) (fun p => continuation β g K k (p k))
      then Act.stop else Act.go
    else Act.go]

noncomputable def gridPolicy {n T : ℕ} (μ : Measure (Fin T → Cube n)) (β : ℝ)
    (g : Fin T → Cube n → ℝ) (K : Fin T → Kernel (Cube n) (Cube n)) (m : ℕ) :
    Fin T → Cube n → Act :=
  fun k => (gridPrefix μ β g K m T).getD k.val (fun _ => Act.go)

/-- i=0 is the Bellman policy; i=T is the approximating policy. -/
noncomputable def intermediatePolicy {n T : ℕ} (μ : Measure (Fin T → Cube n)) (β : ℝ)
    (g : Fin T → Cube n → ℝ) (K : Fin T → Kernel (Cube n) (Cube n)) (m i : ℕ) :
    Fin T → Cube n → Act :=
  fun k x => if k.val < i then gridPolicy μ β g K m k x else optimalPolicy β g K k x

/-- Nonnegative subdivision levels, including zero coefficient and large-error cases. -/
noncomputable def gridLevels (n T : ℕ) (L lam ε : ℝ) : ℕ :=
  ⌈Real.log (max 1 (2 * T * L * lam * Real.sqrt n / ε)) / Real.log 2⌉₊

end InterpOptStop.SAA.Supplement


