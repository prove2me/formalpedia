-- Prove2me | Definitions.Def_DQILocal_Recon_Reconstruction
-- name    : DQILocal_Recon_Reconstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:24.337464+00:00
-- url     : https://prove2.me/theorems/3b7bed1e-5bce-460b-9a87-835b54bd5d92
-- title:
--   The primal tree $\mathcal T'_t$, the planted model, the root posterior $M^{(t)}$, (non-)reconstruction, $\beta_d$ and $\bar{\mathfrak m}_t$
-- statement:
--   $\mathcal T'_t$ is the tree rooted at a primal variable $a_0$ with $D-1$ child clauses; every clause has $k-1$ child variables, every non-root variable above the leaves has $D-1$ child clauses, and the leaves are the variables after $t$ clause layers. For a clause $j$, $\partial j$ is the set of its $k$ variables.
--
--   **Planted model.** Draw the variable values $z^\star$ uniformly and, independently for each clause $j$, $u_j\sim p$. Reveal $w_j=u_j-\sum_{a\in\partial j}z^\star_a$ for each clause and $z^\star_a$ for every leaf. The posterior law of the variable values is the primal Gibbs measure on the tree with clause weights $p\bigl(\sum_{a\in\partial j}z_a+w_j\bigr)$ and the leaves fixed, and the root posterior relative to the truth is
--
--   $$M^{(t)}(x)=\Pr\bigl[z_{a_0}=z^\star_{a_0}+x\bigm|\text{observations}\bigr],\qquad x\in\mathbb Z_q .$$
--
--   The primal model at $(k,D,q,f,\beta)$ has **non-reconstruction** (Definition 4.4) if $M^{(t)}\to\mathrm u$ in probability as $t\to\infty$, and **reconstruction** otherwise. The **reconstruction threshold** (Definition 4.8) is $\beta_d=\sup\mathcal N\in[0,\infty]$, where $\mathcal N$ is the set of $\beta\ge0$ with non-reconstruction. For $q=2$ the **mean posterior bias** is $\bar{\mathfrak m}_t=\mathbb E\,\mathfrak m_t$ with $\mathfrak m_t=M^{(t)}(0)-M^{(t)}(1)$, and $\bar{\mathfrak m}_\infty=\lim_t\bar{\mathfrak m}_t$.
--
--   **Formalization Note** The planted space is finite; probabilities and expectations are finite weighted sums, and $M^{(t)}$ is the explicit ratio of two sums (the denominator is positive since $p_\beta>0$). Convergence in probability uses the sup norm on $\mathbb R^{\mathbb Z_q}$ (all norms are equivalent). $\beta_d$ is an `ENNReal` supremum. $\bar{\mathfrak m}_\infty$ is written as $\inf_t\bar{\mathfrak m}_t$, the limit of the nonincreasing sequence; $\bar{\mathfrak m}_t$ is defined by the same formula for every $q$.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §4.3 and Definition 4.4, p. 25; Definition 4.8, p. 28; §4.6, p. 29

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_TreeCode

namespace DQILocal.Recon

open scoped BigOperators
open Filter Topology

/-- **The primal tree `T'_t`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §4.3, p. 25: "Let
`T'_t` be the tree rooted at a primal variable `a₀` that has `D - 1` child clauses. Every clause has
`k - 1` child variables, and every non-root variable above the leaves has `D - 1` child clauses. The
leaves are the variables after `t` clause layers."

Vertices are index paths (`List ℕ`): the root variable is `[]`, the child clauses of a variable `v`
are `v ++ [a]` (`a < D - 1`), the child variables of a clause `j` are `j ++ [b]` (`b < k - 1`).
`varLayer k D d` is the set of variables after `d` clause layers. -/
def varLayer (k D : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | d + 1 => (varLayer k D d).biUnion fun v =>
      ((Finset.range (D - 1)) ×ˢ (Finset.range (k - 1))).image fun ab => v ++ [ab.1, ab.2]

/-- The clauses that are children of the variables after `d` clause layers. -/
def clauseLayer (k D d : ℕ) : Finset (List ℕ) :=
  (varLayer k D d).biUnion fun v => (Finset.range (D - 1)).image fun a => v ++ [a]

/-- The variables of `T'_t`. -/
def primalVars (k D t : ℕ) : Finset (List ℕ) := (Finset.range (t + 1)).biUnion (varLayer k D)

/-- The clauses of `T'_t`. -/
def primalClauses (k D t : ℕ) : Finset (List ℕ) := (Finset.range t).biUnion (clauseLayer k D)

/-- The root variable `a₀` of `T'_t`. -/
def primalRoot (k D t : ℕ) : primalVars k D t :=
  ⟨[], by
    simp only [primalVars, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨0, Nat.succ_pos t, by simp [varLayer]⟩⟩

/-- The sample space of the planted model on `T'_t`: the hidden assignment `z★` of the variables
and the clause noise `u`. -/
abbrev PlantedSpace (q k D t : ℕ) := (primalVars k D t → ZMod q) × (primalClauses k D t → ZMod q)

/-- `Σ_{a ∈ ∂j} z_a`: the sum of the values of the `k` variables of the clause `j` (its parent
variable and its `k - 1` child variables). -/
noncomputable def clauseSum {q k D t : ℕ} (z : primalVars k D t → ZMod q)
    (j : primalClauses k D t) : ZMod q := by
  classical
  exact ∑ a : primalVars k D t, if treeAdj a.1 j.1 then z a else 0

/-- **The planted model (§4.3, p. 25).** The probability of a planted outcome `(z★, u)`: `z★`
uniform on `ℤ_q^{variables}` and, independently for each clause `j`, `u_j ~ p`. -/
noncomputable def plantedWeight {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ)
    (ω : PlantedSpace q k D t) : ℝ :=
  (1 / (q : ℝ) ^ (primalVars k D t).card) * ∏ j, p (ω.2 j)

/-- Probability of an event in the planted model on `T'_t`. -/
noncomputable def plantedProb {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ)
    (E : PlantedSpace q k D t → Prop) : ℝ := by
  classical
  exact ∑ ω : PlantedSpace q k D t, if E ω then plantedWeight k D t p ω else 0

/-- Expectation in the planted model on `T'_t`. -/
noncomputable def plantedExpect {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ)
    (g : PlantedSpace q k D t → ℝ) : ℝ :=
  ∑ ω : PlantedSpace q k D t, plantedWeight k D t p ω * g ω

/-- **The root posterior relative to the truth (§4.3, p. 25).** The observations are
`w_j = u_j - Σ_{a ∈ ∂j} z★_a` for every clause and `z★_a` for every leaf; given them, the posterior
of the variable values is the primal Gibbs measure on the tree with clause weights
`p(Σ_{a ∈ ∂j} z_a + w_j)` and the leaves fixed, and
`M^{(t)}(x) = Pr[z_{a₀} = z★_{a₀} + x | observations]`.

**Formalization Note.** Written as the ratio of the two finite sums. The denominator is positive
when `p > 0` (the term `z = z★` equals `Π_j p(u_j)`), which holds at every finite `β`. -/
noncomputable def rootPosterior {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ)
    (ω : PlantedSpace q k D t) (x : ZMod q) : ℝ := by
  classical
  exact
    let w : primalClauses k D t → ZMod q := fun j => ω.2 j - clauseSum ω.1 j
    let wt : (primalVars k D t → ZMod q) → ℝ := fun z => ∏ j, p (clauseSum z j + w j)
    let ok : (primalVars k D t → ZMod q) → Prop :=
      fun z => ∀ a : primalVars k D t, a.1 ∈ varLayer k D t → z a = ω.1 a
    (∑ z : primalVars k D t → ZMod q,
        if ok z ∧ z (primalRoot k D t) = ω.1 (primalRoot k D t) + x then wt z else 0) /
      (∑ z : primalVars k D t → ZMod q, if ok z then wt z else 0)

/-- **Non-reconstruction (Definition 4.4, p. 25).** The primal model at `(k, D, q, f, β)` has
non-reconstruction if `M^{(t)} → u` in probability as `t → ∞`: for every `ε > 0`,
`Pr[‖M^{(t)} - u‖ > ε] → 0`, with `p = p_β`.

**Formalization Note.** `‖·‖` is the sup norm on `ℝ^{ℤ_q}` (all norms on this finite-dimensional
space are equivalent, so the choice does not matter). -/
def NonRecon (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun t => plantedProb k D t (gibbsWeight q f β)
    (fun ω => ε < ‖rootPosterior k D t (gibbsWeight q f β) ω - unif q‖)) atTop (𝓝 0)

/-- **Reconstruction**: not non-reconstruction (Definition 4.4, p. 25). -/
def HasRecon (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) : Prop := ¬ NonRecon k D q f β

/-- **The reconstruction threshold (Definition 4.8, p. 28)**: `β_d = sup 𝒩 ∈ [0, ∞]`, where `𝒩` is
the set of `β ≥ 0` at which the primal model has non-reconstruction. -/
noncomputable def betaD (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) : ENNReal :=
  ⨆ (β : ℝ) (_ : 0 ≤ β ∧ NonRecon k D q f β), ENNReal.ofReal β

/-- **The mean posterior bias (§4.6, p. 29)**: `m̄_t = E 𝔪_t` with `𝔪_t = M^{(t)}(0) - M^{(t)}(1)`.

**Formalization Note.** Defined for every `q` by the same formula; the paper uses it for `q = 2`. -/
noncomputable def mbar (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) (t : ℕ) : ℝ :=
  plantedExpect k D t (gibbsWeight q f β)
    (fun ω => rootPosterior k D t (gibbsWeight q f β) ω 0 -
      rootPosterior k D t (gibbsWeight q f β) ω 1)

/-- `m̄_∞ = lim_{t→∞} m̄_t` (Corollary 4.11, p. 29), written as `inf_t m̄_t`.

**Formalization Note.** For `q = 2`, `m̄_t` is nonincreasing in `t` and lies in `[0, 1]` (p. 29), so
the infimum is the limit; the sequence is bounded below by `-1` for every `q`, so `⨅` is the true
infimum. -/
noncomputable def mbarInf (k D q : ℕ) [NeZero q] (f : ZMod q → ℝ) (β : ℝ) : ℝ :=
  ⨅ t : ℕ, mbar k D q f β t

end DQILocal.Recon


