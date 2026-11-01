-- Prove2me | Definitions.Def_AssignToSeatRM_DynamicPrimal
-- name    : AssignToSeatRM_DynamicPrimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:05.562899+00:00
-- url     : https://prove2.me/theorems/85ef2fbc-27cf-427e-a433-b5cc347acbb3
-- title:
--   The dynamic primal (14), the constraints (15), OPT$(A,d,\hat\gamma)$ of (EC.18) and RDP's options
-- statement:
--   Fix right-hand sides $A_{uv}$ (counts of maximal sequences $[u,v]$) and demands $d_{ij}$. The variable $\gamma_{uijv}$ ($u\le i\le j\le v$) is the number of requests $i\to j$ put into a maximal sequence $[u,v]$, and $\gamma_{0ij0}$ the number of requests $i\to j$ rejected.
--
--   **(EC.18)**, with lower bounds $\hat\gamma\ge0$: maximize $\sum_{i\le j}p_{ij}\sum_{(u,v):u\le i\le j\le v}\gamma_{uijv}$ subject to
--
--   $$\sum_{(u,v):\,u\le i\le j\le v}\gamma_{uijv}+\gamma_{0ij0}=d_{ij}\quad(i\le j),$$
--
--   $$\sum_{(i,j):\,u\le i\le j\le v}\gamma_{uijv}\ \le\ \sum_{(k,\ell):\,v+1\le k\le \ell}\gamma_{u(v+1)k\ell}+\sum_{(k,\ell):\,\ell\le k\le u-1}\gamma_{\ell k(u-1)v}+A_{uv}\quad(u\le v),$$
--
--   $$\gamma_{uijv}\ge\hat\gamma_{uijv},\qquad\gamma_{0ij0}\ge\hat\gamma_{0ij0}.$$
--
--   Its optimal value is $\mathrm{OPT}(A,d,\hat\gamma)$; the **dynamic primal (14)** is the case $\hat\gamma=0$. The second constraint says that the number of times $[u,v]$ is consumed does not exceed the number of times it is generated (by splitting longer sequences) plus the number available at the start.
--
--   **(15)** for a realized request $i\to j$: $\gamma_{uijv}\le A_{uv}$ for every $(u,v)$ with $u\le i\le j\le v$. An optimal solution of (14)+(15) is optimal among the solutions satisfying both.
--
--   **Options of RDP** (Algorithm 3, line 4): for a request $i\to j$ the options are rejection $[0,0]$, with value $\gamma_{0ij0}$, and the pairs $(u,v)$ with $u\le i\le j\le v$, with value $\gamma_{uijv}$; RDP picks an option of maximal value, ties broken arbitrarily. The module also defines the sup-norm over a finite index set used in Lemma EC.5.
--
--   **Formalization Note** A solution is a function on quadruples of naturals that vanishes outside the index set of the LP; this fixes coordinates that are not variables and changes no objective value. Optimal values are suprema over the feasible set; "optimal solution" is defined without the supremum.
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, (14) p.19, (15) and Algorithm 3 p.20, (EC.18) p.ec18, Lemma EC.5 p.ec21 (sup-norm)

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # The dynamic primal (14), the constraints (15) and the variant OPT(A, d, γ̂) of (EC.18)

Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023, doi:10.1287/msom.2023.1188, (14)
(p.19), (15) and Algorithm 3 (p.20), (EC.18) (p.ec18).

**Formalization Note.**
1. A solution is `γ : Idx4 → ℝ`, `γ (u, i, j, v) = γ_{uijv}`, and `γ (0, i, j, 0) = γ_{0ij0}` is
   the number of rejected requests `i → j`. The coordinates outside `gammaIdx M` are not
   variables of the LP; the feasible set fixes them to `0`, which changes no objective value and
   makes the feasible set a subset of a finite-dimensional space.
2. `A : ℕ → ℕ → ℝ` holds the right-hand sides `A_{uv}` and `d : ℕ → ℕ → ℝ` the demands `d_{ij}`;
   in the paper `A` is `f(C)` (natural numbers) and `d` is an expected or realized demand.
3. `OPT M p A d γ̂` is the optimal value of (EC.18): (14) with the lower bounds
   `γ_{uijv} ≥ γ̂_{uijv}`, `γ_{0ij0} ≥ γ̂_{0ij0}` in place of `γ ≥ 0`. The paper uses it only for
   `γ̂ ≥ 0`, and (14) is `OPT(A, d, 0)` (p.ec18). The value is the `sSup` of the objective over
   the feasible set; "optimal solution" is stated directly (`IsOptimalOPT`), without `sSup`.
4. In the second group of constraints of (14) the generated maximal sequences `[u, v]` are
   `Σ_{(k,ℓ): v+1 ≤ k ≤ ℓ} γ_{u(v+1)kℓ}` (a request `v+1 → k` put into some `[u, ℓ]`) and
   `Σ_{(k,ℓ): ℓ ≤ k ≤ u−1} γ_{ℓk(u−1)v}` (a request `k → u−1` put into some `[ℓ, v]`), with
   `1 ≤` every index `≤ M`; both sums are empty at the boundary (`v = M`, resp. `u = 1`). -/

/-- `Σ_{(u,v): u ≤ i ≤ j ≤ v} γ_{uijv}`: the requests `i → j` that are allocated. -/
def allocated (M : ℕ) (γ : Idx4 → ℝ) (i j : ℕ) : ℝ :=
  ∑ uv ∈ envs M i j, γ (uv.1, i, j, uv.2)

/-- `Σ_{(i,j): u ≤ i ≤ j ≤ v} γ_{uijv}`: the number of times a maximal sequence `[u, v]` is
consumed. -/
def consumed (M : ℕ) (γ : Idx4 → ℝ) (u v : ℕ) : ℝ :=
  ∑ ij ∈ reqsIn M u v, γ (u, ij.1, ij.2, v)

/-- `Σ_{(k,ℓ): v+1 ≤ k ≤ ℓ} γ_{u(v+1)kℓ} + Σ_{(k,ℓ): ℓ ≤ k ≤ u−1} γ_{ℓk(u−1)v}`: the number of
times a maximal sequence `[u, v]` is generated (p.19). -/
def generated (M : ℕ) (γ : Idx4 → ℝ) (u v : ℕ) : ℝ :=
  ∑ kl ∈ (itins M).filter (fun kl => v + 1 ≤ kl.1), γ (u, v + 1, kl.1, kl.2) +
    ∑ lk ∈ (itins M).filter (fun lk => lk.2 + 1 ≤ u), γ (lk.1, lk.2, u - 1, v)

/-- The objective of (14) and (EC.18): `Σ_{i ≤ j} p_{ij} Σ_{(u,v): u ≤ i ≤ j ≤ v} γ_{uijv}`. -/
def dpObjective (M : ℕ) (p : ℕ → ℕ → ℝ) (γ : Idx4 → ℝ) : ℝ :=
  ∑ ij ∈ itins M, p ij.1 ij.2 * allocated M γ ij.1 ij.2

/-- The constraints of (EC.18) (p.ec18), i.e. of (14) (p.19) with lower bounds `γ̂`:
1. `Σ_{(u,v): u ≤ i ≤ j ≤ v} γ_{uijv} + γ_{0ij0} = d_{ij}` for every `i ≤ j`;
2. `Σ_{(i,j): u ≤ i ≤ j ≤ v} γ_{uijv} ≤ Σ_{(k,ℓ): v+1 ≤ k ≤ ℓ} γ_{u(v+1)kℓ}
   + Σ_{(k,ℓ): ℓ ≤ k ≤ u−1} γ_{ℓk(u−1)v} + A_{uv}` for every `u ≤ v`;
3. `γ_{uijv} ≥ γ̂_{uijv}` and `γ_{0ij0} ≥ γ̂_{0ij0}`;
4. (encoding) `γ` vanishes outside the index set `gammaIdx M`. -/
def IsFeasOPT (M : ℕ) (A d : ℕ → ℕ → ℝ) (γhat γ : Idx4 → ℝ) : Prop :=
  (∀ ij ∈ itins M, allocated M γ ij.1 ij.2 + γ (0, ij.1, ij.2, 0) = d ij.1 ij.2) ∧
  (∀ uv ∈ itins M, consumed M γ uv.1 uv.2 ≤ generated M γ uv.1 uv.2 + A uv.1 uv.2) ∧
  (∀ c ∈ gammaIdx M, γhat c ≤ γ c) ∧
  (∀ c, c ∉ gammaIdx M → γ c = 0)

/-- `OPT(A, d, γ̂)` (p.ec18): the optimal value of (EC.18). -/
def OPT (M : ℕ) (p A d : ℕ → ℕ → ℝ) (γhat : Idx4 → ℝ) : ℝ :=
  sSup (dpObjective M p '' {γ | IsFeasOPT M A d γhat γ})

/-- `γ` is an optimal solution of (EC.18) (of (14) when `γ̂ = 0`). -/
def IsOptimalOPT (M : ℕ) (p A d : ℕ → ℕ → ℝ) (γhat γ : Idx4 → ℝ) : Prop :=
  IsFeasOPT M A d γhat γ ∧
    ∀ γ' : Idx4 → ℝ, IsFeasOPT M A d γhat γ' → dpObjective M p γ' ≤ dpObjective M p γ

/-- The optimal value of the dynamic primal (14) (p.19): `OPT(A, d, 0)`. -/
def lp14Value (M : ℕ) (p A d : ℕ → ℕ → ℝ) : ℝ :=
  OPT M p A d 0

/-- The constraints (15) (p.20) for the realized request `i → j`:
`γ_{uijv} ≤ A_{uv}` for every `(u, v)` with `u ≤ i ≤ j ≤ v`. -/
def Sat15 (M : ℕ) (A : ℕ → ℕ → ℝ) (i j : ℕ) (γ : Idx4 → ℝ) : Prop :=
  ∀ uv ∈ envs M i j, γ (uv.1, i, j, uv.2) ≤ A uv.1 uv.2

/-- `γ` is an optimal solution of (14) together with (15) for the request `i → j`
(Algorithm 3, line 3, p.20): it satisfies (14) and (15), and its objective is at least that of
every solution satisfying (14) and (15). -/
def IsOptimal1415 (M : ℕ) (p A d : ℕ → ℕ → ℝ) (i j : ℕ) (γ : Idx4 → ℝ) : Prop :=
  (IsFeasOPT M A d 0 γ ∧ Sat15 M A i j γ) ∧
    ∀ γ' : Idx4 → ℝ, IsFeasOPT M A d 0 γ' ∧ Sat15 M A i j γ' →
      dpObjective M p γ' ≤ dpObjective M p γ

/-- The options of Algorithm 3, line 4 (p.20) for a request `i → j`: reject (`none`, the pair
`[0, 0]`) or a pair `some (u, v)` with `u ≤ i ≤ j ≤ v`. -/
def options (M i j : ℕ) : Finset (Option (ℕ × ℕ)) :=
  insert none ((envs M i j).image some)

/-- The coordinate of `γ` that an option selects for the request `i → j`: `γ_{0ij0}` for
rejection, `γ_{uijv}` for `(u, v)`. -/
def optionValue (γ : Idx4 → ℝ) (i j : ℕ) : Option (ℕ × ℕ) → ℝ
  | none => γ (0, i, j, 0)
  | some uv => γ (uv.1, i, j, uv.2)

/-- `o` is an `argmax` of `γ_{u i j v}` over the options of Algorithm 3, line 4 (p.20), the
rejection `[0, 0]` included; ties may be broken arbitrarily. -/
def IsMaxOption (M : ℕ) (γ : Idx4 → ℝ) (i j : ℕ) (o : Option (ℕ × ℕ)) : Prop :=
  o ∈ options M i j ∧ ∀ o' ∈ options M i j, optionValue γ i j o' ≤ optionValue γ i j o

/-- The sup-norm `max_{a ∈ s} |f a|` over a finite index set (`0` on the empty set). -/
def supNormOn {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ((s.sup fun a => ‖f a‖₊ : NNReal) : ℝ)

end AssignToSeatRM


