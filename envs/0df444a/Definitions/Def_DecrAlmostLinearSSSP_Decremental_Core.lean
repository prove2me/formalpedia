-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Core
-- name    : DecrAlmostLinearSSSP_Decremental_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:40.623913+00:00
-- url     : https://prove2.me/theorems/4a73924c-0aef-4a52-83ff-56dec6fb1f8e
-- title:
--   Normalized decremental core, return edges and fixed parameters
-- statement:
--   The internal construction has $m\ge n\ge2$, $1/m<\epsilon<1$, initially source-reachable vertices, and no edge entering the source. A fixed polynomial exponent bounds $W$. These are internal conditions, not restrictions on the final goal. Set
--
--   $$H=4nW,\quad Q=8nH=32n^2W,\quad A=\left\lceil\frac{32\log_2(m+1)}{\epsilon}\right\rceil,\quad \kappa=(AmQ)^{-2}.$$
--
--   Every core edge remains present: its cost is $w_e/Q$ while active and $H/Q$ after deletion. A distinct zero-cost return edge $r_v:v\to s$ is added for each nonsource vertex. Let $q(v)$ be its initial core indegree and $q(s)=0$; coefficients are $\mu_e=1$ on core edges and $\mu_{r_v}=Aq(v)$. Initial labels are $p_s^0=0$, $p_v^0=1/(2Q)$. The scalar output is $\infty$ when $Qr>H/2$, and $(1+\epsilon/2)Qr$ otherwise.
--
--   These shared definitions preserve the deleted-edge sentinel and the paper's exact constants. **Formalization Note** Public completed-state outputs use extended nonnegative reals. Conversion of a negative intermediate scalar to zero is a total extension; stable-state positivity is a theorem obligation and makes this extension unobservable at public boundaries.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp. 7–8, §3.1, equations (3.1)–(3.7); pp. 9–10, equations (3.13), (3.15); pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Internal §3 instance: no vertex is discarded silently. Full-domain preprocessing belongs
outside this structure. These assumptions never occur in `Input.Valid`. -/
structure Core where
  input : Input
  valid : input.Valid
  two : 2 ≤ input.n
  epsilon_low : 1 / (input.size : ℝ) < input.accuracy
  epsilon_high : input.accuracy < 1
  initially_reachable : ∀ v, Reachable input.graph Finset.univ input.source v
  no_incoming_source : ∀ e, input.graph.head e ≠ input.source
  weightExponent : ℕ
  weightRange : input.W ≤ input.size ^ weightExponent

noncomputable def H (b : Core) : ℝ := 4 * b.input.n * b.input.W
noncomputable def Q (b : Core) : ℝ := 8 * b.input.n * H b
noncomputable def A (b : Core) : ℝ :=
  (⌈32 * logarithm2 (b.input.size + 1) / b.input.accuracy⌉₊ : ℝ)
noncomputable def kappa (b : Core) : ℝ := (A b * b.input.size * Q b) ^ (-2 : ℤ)

def ReturnVertex (b : Core) := {v : Fin b.input.n // v ≠ b.input.source}
abbrev Edge (b : Core) := Fin b.input.k ⊕ ReturnVertex b

instance (b : Core) : Fintype (ReturnVertex b) := by unfold ReturnVertex; infer_instance
instance (b : Core) : DecidableEq (ReturnVertex b) := by unfold ReturnVertex; infer_instance

def tail (b : Core) : Edge b → Fin b.input.n
  | .inl e => b.input.graph.tail e
  | .inr v => v.val

def head (b : Core) : Edge b → Fin b.input.n
  | .inl e => b.input.graph.head e
  | .inr _ => b.input.source

noncomputable def indegree (b : Core) (v : Fin b.input.n) : ℕ :=
  if v = b.input.source then 0 else (Finset.univ.filter fun e => b.input.graph.head e = v).card

noncomputable def coefficient (b : Core) : Edge b → ℝ
  | .inl _ => 1
  | .inr v => A b * indegree b v.val

noncomputable def cost (b : Core) (active : Finset (Fin b.input.k)) : Edge b → ℝ
  | .inl e => if e ∈ active then (b.input.weight e : ℝ) / Q b else H b / Q b
  | .inr _ => 0

noncomputable def coreDistance (b : Core) (active : Finset (Fin b.input.k))
    (v : Fin b.input.n) : ℝ≥0∞ :=
  distance b.input.graph Finset.univ (fun e => ENNReal.ofReal (cost b active (.inl e)))
    b.input.source v

noncomputable def initialLabel (b : Core) (v : Fin b.input.n) : ℝ :=
  if v = b.input.source then 0 else 1 / (2 * Q b)

noncomputable def readout (b : Core) (r : ℝ) : ℝ≥0∞ :=
  if Q b * r > H b / 2 then ⊤ else ENNReal.ofReal ((1 + b.input.accuracy / 2) * Q b * r)

end DecrAlmostLinearSSSP.Decremental


