-- Prove2me | Definitions.Def_FiniteMemPOMDP_lawOfPlays
-- name    : FiniteMemPOMDP_lawOfPlays
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:56.052983+00:00
-- url     : https://prove2.me/theorems/797c2c94-1636-4e33-920a-b7f297300850
-- title:
--   The law $\mathbb P^{p_1}_\sigma$ of plays
-- statement:
--   Fix a POMDP $\Gamma$, an initial belief $p_1\in\Delta(\mathcal K)$ and a (pure) strategy $\sigma:\bigcup_{m\ge1}\mathcal H_m\to\mathcal A$, where $\mathcal H_m=(\mathcal A\times\mathcal S)^{m-1}$ is the set of histories before stage $m$. The play proceeds as follows:
--
--   1. the initial state $K_1$ is drawn from $p_1$;
--   2. at stage $m\ge1$, the decision-maker plays $A_m=\sigma(H_m)$, where $H_m=((A_1,S_1),\dots,(A_{m-1},S_{m-1}))$;
--   3. the pair $(K_{m+1},S_m)$ is drawn from $q(K_m,A_m)$.
--
--   $\mathbb P^{p_1}_\sigma$ is the law of the resulting play, a probability measure on the play space.
--
--   **Formalization Note** The measure is Mathlib's Ionescu-Tulcea trajectory measure `Kernel.trajMeasure`, with initial law $K_1\sim p_1$ and one step kernel per stage. A strategy is a function `List (A × S) → A` on chronological histories, defined on histories of every length. A verification lemma checks that $\mathbb P^{p_1}_\sigma(K_1=k)=p_1(k)$.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib
import Definitions.Def_FiniteMemPOMDP_POMDP
import Definitions.Def_FiniteMemPOMDP_PlayStep
import Definitions.Def_FiniteMemPOMDP_beliefPMF

open MeasureTheory ProbabilityTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S]

/-- The history `((A_1, S_1), …, (A_n, S_n))` recorded in the first `n + 1` coordinates of a
partial play (coordinates `1, …, n`; coordinate `0` holds only the initial state). -/
def prefixHistory (n : ℕ) (x : Π _ : Finset.Iic n, PlayStep A S K) : List (A × S) :=
  List.ofFn fun j : Fin n =>
    let y := x ⟨j.1 + 1, Finset.mem_Iic.mpr j.2⟩
    (y.act, y.sig)

/-- **One stage of play.** Given the partial play `x` up to coordinate `n` (the history `h` of
length `n` and the current state `k = K_{n+1}`), the decision-maker plays `a = σ h`, and the pair
`(K_{n+2}, S_{n+1})` is drawn from `q(k, a)`; the kernel returns the coordinate
`(a, S_{n+1}, K_{n+2})`. -/
noncomputable def stepKernel (Γ : POMDP K A S) (σ : List (A × S) → A) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, PlayStep A S K) (PlayStep A S K) :=
  Kernel.ofFunOfCountable fun x =>
    let k : K := (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).state
    let a : A := σ (prefixHistory n x)
    ((Γ.q k a).map fun ks : K × S => PlayStep.mk a ks.2 ks.1).toMeasure

instance (Γ : POMDP K A S) (σ : List (A × S) → A) (n : ℕ) :
    IsMarkovKernel (stepKernel Γ σ n) :=
  ⟨fun _ => by unfold stepKernel; simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]; infer_instance⟩

/-- The law of the initial coordinate: `K_1 ∼ p` (with the dummy action and signal). -/
noncomputable def initialLaw [Nonempty A] [Nonempty S] (p : stdSimplex ℝ K) :
    Measure (PlayStep A S K) :=
  ((beliefPMF p).map fun k => PlayStep.mk (Classical.arbitrary A) (Classical.arbitrary S) k).toMeasure

instance [Nonempty A] [Nonempty S] (p : stdSimplex ℝ K) :
    IsProbabilityMeasure (initialLaw (A := A) (S := S) p) := by
  unfold initialLaw; infer_instance

/-- **The law `P^{p1}_σ` of plays.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2: "For p1 ∈ ∆(K) and σ ∈ Σ, define
P^{p1}_σ the law induced by σ and the initial belief p1 on the set of plays of the game
Ω = (K × A × S)^ℕ". The dynamics (p.2): "An initial state K1 is drawn from p1 … At each stage
m ≥ 1, the decision-maker takes some action Am ∈ A … Then, the pair (Km+1, Sm) is drawn from
q(Km, Am)", where `A_m = σ(H_m)` for the pure strategy `σ`.

`lawOfPlays Γ p σ` is the Ionescu-Tulcea measure on `ℕ → PlayStep A S K` with initial law
`K_1 ∼ p` and step kernels `stepKernel Γ σ`: coordinate `n + 1` is `(A_{n+1}, S_{n+1}, K_{n+2})`
with `A_{n+1} = σ((A_1, S_1), …, (A_n, S_n))` and `(K_{n+2}, S_{n+1}) ∼ q(K_{n+1}, A_{n+1})`.

**Formalization Note** A strategy is a map `List (A × S) → A` on histories in chronological
order (`H_m = (A × S)^{m−1}` is the set of lists of length `m − 1`). The play space is
`ℕ → PlayStep A S K`, a re-indexing of `(K × A × S)^ℕ` (see `PlayStep`). The measure is built with
Mathlib's `ProbabilityTheory.Kernel.trajMeasure` and is a probability measure (instance below). -/
noncomputable def lawOfPlays [Nonempty A] [Nonempty S] (Γ : POMDP K A S) (p : stdSimplex ℝ K)
    (σ : List (A × S) → A) : Measure (ℕ → PlayStep A S K) :=
  Kernel.trajMeasure (initialLaw p) (stepKernel Γ σ)

instance [Nonempty A] [Nonempty S] (Γ : POMDP K A S) (p : stdSimplex ℝ K)
    (σ : List (A × S) → A) : IsProbabilityMeasure (lawOfPlays Γ p σ) := by
  unfold lawOfPlays; infer_instance

end FiniteMemPOMDP


