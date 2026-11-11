-- Prove2me | Definitions.Def_NodeStableProj_Main_FastForward
-- name    : NodeStableProj_Main_FastForward
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:55.240227+00:00
-- url     : https://prove2.me/theorems/a725ec75-6e94-42b4-a90e-57f0173aa07e
-- title:
--   The fast-forwarded SVT detector (Algorithm 4) and projection (Algorithm 5)
-- statement:
--   For $V=[n]$, $u\in V$ and $v\ne u$, $\pi_u(v)=v$ if $v<u$ and $\pi_u(v)=v-1$ if $v>u$: the position of the pair $\{u,v\}$ in $t(u)$'s update stream.
--
--   **Algorithm 4.** A fast-forwardable detector keeps $\mathrm{count}=0$, flag $\bot$, a local clock $s=1$ and $\hat\tau=\tau+\eta$, $\eta\sim\mathrm{Lap}(2/\tilde\varepsilon)$. $\mathrm{skip\text{-}to}(r)$: if the flag is $\bot$ and $s<r$, let $p_0=\Pr_{\xi\sim\mathrm{Lap}(4/\tilde\varepsilon)}[\mathrm{count}+\xi>\hat\tau]$, draw $J\sim\mathrm{Geom}(p_0)$ on $\{1,2,\dots\}$ and raise the flag if $J\le r-s$; then $s\leftarrow r$. $\mathrm{process}(a)$, $a\in\{0,1\}$: as $\mathrm{increment}(a)$ of Algorithm 2, then $s\leftarrow s+1$.
--
--   **Algorithm 5.** With $\tau=(D+\hat D)/2$ and one fast-forwardable detector per vertex, for each edge $\{u,v\}$ ($u<v$) in lexicographic order: $t(u).\mathrm{skip\text{-}to}(\pi_u(v))$, $t(v).\mathrm{skip\text{-}to}(\pi_v(u))$; if both flags are $\bot$ add the edge to $H$ and $a=1$, else $a=0$; $t(u).\mathrm{process}(a)$, $t(v).\mathrm{process}(a)$. Finally $t(u).\mathrm{skip\text{-}to}(n)$ for every $u$. After every skip-to or process call, if a detector raised its flag while its counter is below $D$, or has counter at least $\hat D$ without its flag, the algorithm returns a maximal $\hat D$-bounded subgraph of $G$ (fallback rule $F$); otherwise it returns $H$.
--
--   **Formalization Note.** Randomness is presampled per detector: $\eta_u$ at index $0$, and the $c$-th operation on $t(u)$ reads a fresh pair $(\xi,U)$, $\xi\sim\mathrm{Lap}(4/\tilde\varepsilon)$, $U$ uniform on $[0,1]$, all independent. $J$ is sampled by inversion, $J=\min\{j\ge1:U\le1-(1-p_0)^j\}$, whose law is exactly $\mathrm{Geom}(p_0)$. The fallback test is accumulated and $F$ applied at the end; continuing after it fires changes nothing that is returned.
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), pp. 30–31, Appendix B, π_u(v), Algorithms 4 and 5

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_Graph
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-!
# The fast-forwarded detector (Algorithm 4) and projection (Algorithm 5)

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), pp. 30–31 (PDF 32–33),
Appendix B, `π_u(v)`, Algorithms 4 and 5.

**Formalization Note.**
* Algorithm 5 takes `V = [n] = {1, …, n}`; `π_u(v) = v` if `v < u` and `v − 1` if `v > u`.
* Randomness is presampled per detector: `ν u 0` carries `η_u ∼ Lap(2/ε̃)` in its first
  component; the `c`-th operation (`skip-to` or `process`, `c ≥ 1`) on `t(u)` reads
  `ν u c = (ξ, U)` with `ξ ∼ Lap(4/ε̃)` (used by `process`) and `U` uniform on `[0, 1]` (used by
  `skip-to`). All coordinates are independent. A detector receives at most `2(n − 1) + 1`
  operations, so the law is the finite product over `u ∈ V`, `c ≤ 2|V|` (`noise5Law`).
* `J ∼ Geom(p₀)` on `{1, 2, …}` is sampled by inversion from `U`: `J` is the least `j ≥ 1` with
  `U ≤ 1 − (1 − p₀)^j` (`geomOfUniform`); for `U` uniform on `[0, 1]` and `p₀ ∈ (0, 1]` its law is
  exactly `Geom(p₀)`. `p₀ = Pr_{ξ∼Lap(4/ε̃)}[count + ξ > τ̂]` is computed with the Laplace law.
* "After every `skip-to` or `process` call, if a detector raises its flag when its counter is
  below `D`, or reaches `D̂` without raising its flag, return any maximal `D̂`-bounded subgraph"
  is accumulated in `bad` with the same test `badStep` as Algorithm 1, and the fallback rule `F`
  is applied at the end if `bad` ever fired. Continuing the loop after the test fires changes
  nothing that is returned.
-/

/-- The state of a fast-forwardable detector (Algorithm 4): counter, flag, the next local time
step `s`, and the number of operations received (which indexes its randomness). -/
structure FFDetector where
  count : ℝ
  flag : Bool
  s : ℕ
  ops : ℕ

/-- `FF-SVT-initialize`: `count ← 0`, `flag ← ⊥`, `s ← 1`. -/
def FFDetector.init : FFDetector := ⟨0, false, 1, 0⟩

/-- The inversion sampler of `Geom(p)` on `{1, 2, …}`: the least `j ≥ 1` with
`U ≤ 1 − (1 − p)^j` (`0` if there is none, which has probability `0`). -/
noncomputable def geomOfUniform (p U : ℝ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ U ≤ 1 - (1 - p) ^ j}

/-- `skip-to(r)` (Algorithm 4, lines 5–10): if `flag = ⊥` and `s < r`, with
`p₀ = Pr_{ξ∼Lap(4/ε̃)}[count + ξ > τ̂]` and `J ∼ Geom(p₀)`, set `flag ← ⊤` if `J ≤ r − s`;
then `s ← r`. -/
noncomputable def FFDetector.skipTo (τ εt : ℝ) (noise : ℕ → ℝ × ℝ) (r : ℕ) (d : FFDetector) :
    FFDetector :=
  let c := d.ops + 1
  if d.flag = false ∧ d.s < r then
    let p0 : ℝ :=
      (PrivLearn.Generic.laplace (4 / εt) {x | τ + (noise 0).1 < d.count + x}).toReal
    { count := d.count
      flag := decide (geomOfUniform p0 (noise c).2 ≤ r - d.s)
      s := r
      ops := c }
  else { d with s := r, ops := c }

/-- `process(a)` (Algorithm 4, lines 11–16): if `flag = ⊥` then `count ← count + a`,
`ĉ ← count + ξ`, `flag ← ⊤` if `ĉ > τ̂`; then `s ← s + 1`. -/
noncomputable def FFDetector.process (τ : ℝ) (noise : ℕ → ℝ × ℝ) (a : ℝ) (d : FFDetector) :
    FFDetector :=
  let c := d.ops + 1
  if d.flag = false then
    { count := d.count + a
      flag := decide (τ + (noise 0).1 < d.count + a + (noise c).1)
      s := d.s + 1
      ops := c }
  else { d with s := d.s + 1, ops := c }

/-- The detector-state view of an `FFDetector`, for the fallback test `badStep`. -/
def FFDetector.toDetector (d : FFDetector) : Detector := ⟨d.count, d.flag, d.ops⟩

/-- `π_u(v)` (p. 30): `v` if `v < u`, `v − 1` if `v > u`. -/
def piPos (u v : ℕ) : ℕ := if v < u then v else v - 1

/-- The edges of `G` as pairs `(u, v)`, `u < v`, in the lexicographic order of Algorithm 1. -/
noncomputable def lexEdges (G : Graph) : List (ℕ × ℕ) :=
  (lexPairs G.V).filter fun p => decide (s(p.1, p.2) ∈ G.E)

/-- The state of Algorithm 5. -/
structure Alg5State where
  det : ℕ → FFDetector
  H : Finset (Sym2 ℕ)
  bad : Bool

/-- Initial state: every detector `FF-SVT-initialize`d, `H = ∅`. -/
def Alg5State.init : Alg5State := ⟨fun _ => FFDetector.init, ∅, false⟩

/-- Apply an operation to detector `u` and run the fallback test on it. -/
noncomputable def Alg5State.apply (D Dhat : ℝ) (u : ℕ) (f : FFDetector → FFDetector)
    (st : Alg5State) : Alg5State :=
  let d' := f (st.det u)
  { det := Function.update st.det u d'
    H := st.H
    bad := st.bad || badStep D Dhat (st.det u).toDetector d'.toDetector }

/-- One iteration of the main loop of Algorithm 5 (lines 7–17) on the edge `(u, v)`, `u < v`. -/
noncomputable def alg5Step (D Dhat : ℕ) (εt : ℝ) (ν : ℕ → ℕ → ℝ × ℝ) (st : Alg5State)
    (p : ℕ × ℕ) : Alg5State :=
  let u := p.1
  let v := p.2
  let τ : ℝ := ((D : ℝ) + Dhat) / 2
  let st1 := st.apply D Dhat u ((FFDetector.skipTo τ εt (ν u)) (piPos u v))
  let st2 := st1.apply D Dhat v ((FFDetector.skipTo τ εt (ν v)) (piPos v u))
  let add : Bool := !(st2.det u).flag && !(st2.det v).flag
  let a : ℝ := if add then 1 else 0
  let st3 : Alg5State := { st2 with H := if add then insert s(u, v) st2.H else st2.H }
  let st4 := st3.apply D Dhat u (FFDetector.process τ (ν u) a)
  st4.apply D Dhat v (FFDetector.process τ (ν v) a)

/-- The output of Algorithm 5 on `G` (vertex set `[n]`, `n = |V|`), noise `ν`, fallback rule
`F`: the main loop over the lexicographically ordered edges, then `skip-to(n)` on every
detector (lines 18–19), then `H` or, if a fallback test fired, `F G`. -/
noncomputable def alg5Out (D Dhat : ℕ) (εt : ℝ) (F : Graph → Graph) (G : Graph)
    (ν : ℕ → ℕ → ℝ × ℝ) : Graph :=
  let τ : ℝ := ((D : ℝ) + Dhat) / 2
  let st := (lexEdges G).foldl (alg5Step D Dhat εt ν) Alg5State.init
  let st' := (G.V.sort (· ≤ ·)).foldl
    (fun s u => s.apply D Dhat u ((FFDetector.skipTo τ εt (ν u)) G.V.card)) st
  if st'.bad then F G else G.withEdges st'.H

/-- The law of Algorithm 5's randomness on vertex set `V`: independent pairs, with first
coordinate `Lap(2/ε̃)` at index `0` and `Lap(4/ε̃)` at indices `1 … 2|V|`, and second coordinate
uniform on `[0, 1]`. -/
noncomputable def noise5Law (εt : ℝ) (V : Finset ℕ) :
    Measure (↥V → Fin (2 * V.card + 1) → ℝ × ℝ) :=
  Measure.pi fun _ : ↥V =>
    Measure.pi fun c : Fin (2 * V.card + 1) =>
      (PrivLearn.Generic.laplace (if (c : ℕ) = 0 then 2 / εt else 4 / εt)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- A noise vector of Algorithm 5 on `V` read as a function of (vertex, index), `(0, 0)` outside. -/
def extendNoise5 {V : Finset ℕ} (ν : ↥V → Fin (2 * V.card + 1) → ℝ × ℝ) : ℕ → ℕ → ℝ × ℝ :=
  fun u c => if h : u ∈ V then (if hc : c < 2 * V.card + 1 then ν ⟨u, h⟩ ⟨c, hc⟩ else (0, 0))
    else (0, 0)

/-- The output law of Algorithm 5 on `G` with fallback rule `F`. -/
noncomputable def alg5Law (D Dhat : ℕ) (εt : ℝ) (F : Graph → Graph) (G : Graph) :
    Measure Graph :=
  (noise5Law εt G.V).map fun ν => alg5Out D Dhat εt F G (extendNoise5 ν)

end NodeStableProj.Main


