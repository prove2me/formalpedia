-- Prove2me | Definitions.Def_EasyRankOne_Secretary_Survivor
-- name    : EasyRankOne_Secretary_Survivor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:06:21.578804+00:00
-- url     : https://prove2.me/theorems/a9582240-912c-4a2f-84aa-39daf4fd0e4a
-- title:
--   Survivor distributions D_{O,t,H} with background schedules, accepting masses (12), Algorithm 3, survivor set (23) (Definition 5.1, §5, §6.1)
-- statement:
--   Fix $p\in[1/e,1)$. For an ordered set $O$ and a horizon $t\in[p,1]$ (Definition 5.1): draw independent **auxiliary times** $T'_e\sim\mathrm{Unif}[0,t]$, $e\in O$; $e$ is **early** if $T'_e\le p$. A **background schedule** $H$ assigns fixed auxiliary times in $[0,t]$ to some elements of $V\setminus O$; $H_u$ is the set of those with time $\le u$. The **capped spanning time** $\sigma_e$ is the first $u\in[p,t]$ at which
--   $$H_u\cup\{f\in O: f\succ e,\ T'_f\le u\}$$
--   spans $e$, or $t$ if this never happens. Conditional on all auxiliary times each early $e$ survives independently with probability $\ln(\sigma_e/p)$; no late element survives. $\mathcal D_{O,t,H}(A)$ is the probability that the survivor set is $A$; for $0<t\le p$ or $O=\emptyset$ it is the point mass at $\emptyset$. Empty background is omitted ($\mathcal D_{O,t}$); the constant background $\{e\}$ is written $e$. $\sigma_{a,H}$ is the first $u\in[p,t]$ at which $H_u$ spans $a$, or $t$. $H+a$ adds $a$ with time $p$, $H^{a,u}$ with time $u$, keeping the earlier time if $a$ is already present. The **accepting masses (12)** are
--   $$z_{O,e,t}(A)=\begin{cases}\frac pt\,\mathcal D_{O-e,t,e}(A), & t>p,\ e\in\mathrm{Greedy}(O),\\ 0 & \text{otherwise.}\end{cases}$$
--   **Algorithm 3** accepts an arrival $e$ at time $t$ with arrived ordered set $O$ (including $e$) and accepted set $\mathrm{ALG}$ with probability $\frac pt\,\mathcal D_{O-e,t,e}(\mathrm{ALG})/\mathcal D_{O-e,t}(\mathrm{ALG})$ ($0/0=0$) if $t>p$ and $e\in\mathrm{Greedy}(O)$, and rejects otherwise. With $g(u)=p\ln(u/p)$, the **survivor set (23)** of a configuration $x\in[0,t]^O$ is $A_{O,t,H}(x)=\{f\in O: x_f\le g(\sigma_f(x))\}$, $\sigma_f(x)$ being the capped spanning time with auxiliary times $x$.
--
--   **Formalization Note.** A background is `α → Option ℝ` (`none`: not in the background); `bgAdd H a u` adds `a` with time `u`, keeping the minimum, so $H+e$ is `bgAdd H e p` and the constant background $e$ is `bgAdd bgEmpty e p`. "First time" is `sInf` of the set of spanning times in $[p,t]$, and $t$ if that set is empty (`firstSpan`). `survD M p O t H A` is $t^{-|O|}\int_{[0,t]^O}\psi_A(x,t)\,dx$ for $t>p$, $O\neq\emptyset$, $A\subseteq O$, where $\psi_A$ (`survCond`) is the product over $f\in O$ of the conditional survival factors; it is $0$ for $A\not\subseteq O$. `survFamily`, `zSurv`, `algorithm3` (a rule of the continuous-time model), `gfun`, `survSet` are the objects above.
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 16, Definition 5.1 and (12); p. 17, Algorithm 3 and background schedules; p. 18; p. 23, (23)

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_ContinuousTime

open MeasureTheory

/-!
# Survivor distributions with background schedules, the accepting masses (12), Algorithm 3 and
# the survivor set of a configuration

Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, *As Easy as Rank One*, STOC 2027 submission
(manuscript of November 2026, sha256 f74f3f91…), Definition 5.1 p. 16, (12) and Algorithm 3
pp. 16–17, background schedules pp. 17–18, §6.1 (23) p. 23.

Definition 5.1, for an ordered set `O` and horizon `t ∈ [p, 1]` (with `p ∈ [1/e, 1)`):
1. independent auxiliary times `T'_e ∼ Unif[0, t]`, `e ∈ O`; `e` is early if `T'_e ≤ p`;
2. the capped spanning time `σ_e` is the first `u ∈ [p, t]` at which
   `H_u ∪ {f ∈ O : f ≻ e, T'_f ≤ u}` spans `e`, or `t` if never;
3. conditional on all auxiliary times each early `e` survives independently with probability
   `ln(σ_e / p)`; no late element survives.
`D_{O,t,H}(A)` is the probability that the survivor set is `A`; for `0 < t ≤ p` or `O = ∅` it is
the point mass at `∅`.

Encoding.
* A background schedule `H : α → Option ℝ` gives each background element its fixed auxiliary
  time (`none`: not in the background). `H_u = bgAt H u`; `bgAdd H a u` adds `a` with time `u`,
  keeping the earlier time if `a` is already present: `H + a = bgAdd H a p`,
  `H_{a,u} = bgAdd H a u`; the constant background `e` is `bgAdd bgEmpty e p`.
* "First time" is `sInf` of the set of `u ∈ [p, t]` at which the set spans, and `t` when that set
  is empty (`firstSpan`); the spanning sets grow with `u` and change at finitely many times, so
  the infimum is attained.
* `survD M p O t H A` integrates the conditional probability `ψ_A(x, t)` of survivor set `A`
  (a product of Bernoulli factors) against the uniform law of `x` on `[0, t]^O`.
-/

namespace EasyRankOne.Secretary

variable {α : Type*}

/-- A background schedule: the fixed auxiliary time of each background element. -/
abbrev Background (α : Type*) := α → Option ℝ

/-- The empty background. -/
def bgEmpty : Background α := fun _ => none

/-- `H_u`: the background elements whose auxiliary time is at most `u`. -/
def bgAt (H : Background α) (u : ℝ) : Set α := {a | ∃ s, H a = some s ∧ s ≤ u}

/-- Add `a` to the background with auxiliary time `u`, keeping the earlier of the old and new
times if `a` is already in the background. -/
def bgAdd [DecidableEq α] (H : Background α) (a : α) (u : ℝ) : Background α :=
  Function.update H a (some (match H a with
    | some s => min s u
    | none => u))

open Classical in
/-- The first `u ∈ [p, t]` at which `S u` spans `a`, or `t` if this never occurs. -/
noncomputable def firstSpan (M : Matroid α) (p t : ℝ) (S : ℝ → Set α) (a : α) : ℝ :=
  if {u | u ∈ Set.Icc p t ∧ a ∈ M.closure (S u)}.Nonempty then
    sInf {u | u ∈ Set.Icc p t ∧ a ∈ M.closure (S u)}
  else t

/-- `σ_{a,H}`: the first `u ∈ [p, t]` at which `H_u` spans `a`, or `t`. -/
noncomputable def bgSpan (M : Matroid α) (p t : ℝ) (H : Background α) (a : α) : ℝ :=
  firstSpan M p t (bgAt H) a

/-- The capped spanning time `σ_f(x)` of `f` in the ordered set `O` with background `H` and
auxiliary times (configuration) `x`: the first `u ∈ [p, t]` at which
`H_u ∪ {f' ∈ O : f' ≻ f, x_{f'} ≤ u}` spans `f`, or `t`. -/
noncomputable def spanTime [DecidableEq α] (M : Matroid α) (p t : ℝ) (O : List α)
    (H : Background α) (x : α → ℝ) (f : α) : ℝ :=
  firstSpan M p t (fun u => bgAt H u ∪ {f' | ListLarger O f' f ∧ x f' ≤ u}) f

open Classical in
/-- `ψ_A(x, t)`: the probability, over the survival coins only, that the survivor set is `A`,
given the auxiliary times `x` (Definition 5.1, steps 2–3; proof of Lemma 5.4). -/
noncomputable def survCond [DecidableEq α] (M : Matroid α) (p t : ℝ) (O : List α)
    (H : Background α) (x : α → ℝ) (A : Finset α) : ℝ :=
  ∏ f ∈ O.toFinset,
    if f ∈ A then (if x f ≤ p then Real.log (spanTime M p t O H x f / p) else 0)
    else (if x f ≤ p then 1 - Real.log (spanTime M p t O H x f / p) else 1)

open Classical in
/-- The survivor distribution `D_{O,t,H}(A)` (Definition 5.1 with background schedule `H`):
the point mass at `∅` when `t ≤ p` or `O = ∅`; otherwise `t^{-|O|} ∫_{[0,t]^O} ψ_A(x,t) dx` for
`A ⊆ O`, and `0` for `A ⊄ O`. -/
noncomputable def survD [DecidableEq α] (M : Matroid α) (p : ℝ) (O : List α) (t : ℝ)
    (H : Background α) (A : Finset α) : ℝ :=
  if t ≤ p ∨ O = [] then (if A = ∅ then 1 else 0)
  else if A ⊆ O.toFinset then
    (t ^ O.length)⁻¹ * boxInt O.toFinset t (fun x => survCond M p t O H x A)
  else 0

/-- The survivor family with empty background: `D O t A = D_{O,t}(A)`. -/
noncomputable def survFamily [DecidableEq α] (M : Matroid α) (p : ℝ) :
    List α → ℝ → Finset α → ℝ :=
  fun O t A => survD M p O t bgEmpty A

open Classical in
/-- The accepting masses (12): `z_{O,e,t}(A) = (p/t) D_{O−e,t,e}(A)` if `t > p` and
`e ∈ Greedy(O)`, and `0` otherwise (`D_{O−e,t,e}`: constant background `e`). -/
noncomputable def zSurv [DecidableEq α] (M : Matroid α) (p : ℝ) :
    List α → α → ℝ → Finset α → ℝ :=
  fun O e t A =>
    if p < t ∧ e ∈ greedyList M O then (p / t) * survD M p (O.erase e) t (bgAdd bgEmpty e p) A
    else 0

open Classical in
/-- Algorithm 3 (survival secretary rule), as a rule of the continuous-time ordinal model: when
`e` arrives at time `t` with arrived ordered set `O` (including `e`) and accepted set `ALG`,
accept with probability `(p/t) D_{O−e,t,e}(ALG) / D_{O−e,t}(ALG)` (`0/0 = 0`) if `t > p` and
`e ∈ Greedy(O)`, else reject. -/
noncomputable def algorithm3 [DecidableEq α] (M : Matroid α) (p : ℝ) : Rule α :=
  fun O h e t =>
    if p < t ∧ e ∈ greedyList M O then
      (p / t) * survD M p (O.erase e) t (bgAdd bgEmpty e p) (accSet h) /
        survD M p (O.erase e) t bgEmpty (accSet h)
    else 0

/-- `g(u) = p ln(u/p)` (§6.1). -/
noncomputable def gfun (p u : ℝ) : ℝ := p * Real.log (u / p)

/-- The survivor set (23) of a configuration `x ∈ [0, t]^O`:
`A_{O,t,H}(x) = {f ∈ O : x_f ≤ g(σ_f(x))}` (`x_f ≤ p`: early with survival coin `x_f / p`). -/
noncomputable def survSet [DecidableEq α] (M : Matroid α) (p t : ℝ) (O : List α)
    (H : Background α) (x : α → ℝ) : Set α :=
  {f | f ∈ O ∧ x f ≤ gfun p (spanTime M p t O H x f)}

end EasyRankOne.Secretary


