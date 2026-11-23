-- Prove2me | Definitions.Def_RobustAgentsCausal_Basic
-- name    : RobustAgentsCausal_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:31:40.972457+00:00
-- url     : https://prove2.me/theorems/bf9f16fb-8da6-4b45-a0c6-ef14418af112
-- title:
--   Causal Bayesian networks, local interventions, causal influence diagrams and policy oracles
-- statement:
--   Objects of Sections 2.1-2.3 and Appendices A.1-A.3 of Richens and Everitt (2024).
--
--   1. **Chance variables.** Finitely many chance variables $C_i$, $i\in I$; $C_i$ takes the categorical values $0,\dots,k_i-1$. A joint state is $c=(c_i)_{i\in I}$. Two joint states agree on $S\subseteq I$ if their coordinates in $S$ coincide, and a function of $c$ depends only on $S$ if it is equal at any two states that agree on $S$.
--   2. **Graphs (Definition 1).** A graph on $I$ is given by parent sets $\mathrm{Pa}_i\subseteq I$ (edges $C_j\to C_i$ for $j\in\mathrm{Pa}_i$). $C_j$ is a proper ancestor of $C_i$ if there is a directed path $C_j\to\cdots\to C_i$, and the graph is a DAG if no variable is its own proper ancestor.
--   3. **Causal Bayesian networks (Definition 1).** A family of conditional distributions for the graph assigns to each $i$ and joint state $c$ a probability vector $P(\cdot\mid \mathrm{pa}_i)$ on the values of $C_i$ that depends on $c$ only through the parents. The joint law is the Markov factorisation $P(c)=\prod_iP(c_i\mid\mathrm{pa}_i)$.
--   4. **Interventions (Definitions 2, 3).** A local intervention is a family of maps $f_i:\{0,\dots,k_i-1\}\to\{0,\dots,k_i-1\}$, one per variable ($f_i=\mathrm{id}$ means no intervention, a constant $f_i$ is a hard intervention). It replaces each conditional by $P(c_i\mid\mathrm{pa}_i;\sigma)=\sum_{c_i':f_i(c_i')=c_i}P(c_i'\mid\mathrm{pa}_i)$, and $P(c;\sigma)=\prod_iP(c_i\mid\mathrm{pa}_i;\sigma)$. A mixture is a probability vector $w$ on the (finitely many) local interventions, with $P(c;\sigma^*)=\sum_fw_fP(c;\sigma_f)$. A soft intervention on a set $T$ replaces $P(c_i\mid\mathrm{pa}_i)$, $i\in T$, by conditional distributions $P'(c_i\mid\mathrm{pa}^*_i)$ for new parent sets $\mathrm{Pa}^*_i$, provided the modified graph is still acyclic; then $P(c;\sigma)=\prod_{i\in T}P'(c_i\mid\mathrm{pa}^*_i)\prod_{i\notin T}P(c_i\mid\mathrm{pa}_i)$.
--   5. **Decision task (Definition 4, Assumption 1).** The decision $D$ takes values in a finite nonempty set $\mathcal A$; its parents are the chance variables $\mathrm{Pa}_D$, and its only child is the utility $U$, whose parents are $D$ and the chance variables $\mathrm{Pa}_U$. The utility is a real function $U(d,x)$ of $d$ and the configuration $x$ of $\mathrm{Pa}_U$. The chance variables of $\mathrm{Anc}_U$ are those of $\mathrm{Pa}_U\cup\mathrm{Pa}_D$ together with their proper ancestors.
--   6. **Parameters (Appendix A.2).** $\theta_P$ consists of one real number $P(c_i\mid\mathrm{pa}_i)$ for each variable, configuration of its parents and state $c_i\le k_i-2$; it is valid if these numbers are nonnegative and sum to at most $1$, and the last state receives $1-\sum_{c_i\le k_i-2}P(c_i\mid\mathrm{pa}_i)$. $\theta_U$ consists of one real number $U(d,x)$ for each decision and configuration of $\mathrm{Pa}_U$. "Almost all CIDs" refers to Lebesgue measure on the finite-dimensional space of $(\theta_P,\theta_U)$, the graph being fixed.
--   7. **Policies and regret (Section 2.2).** A policy with input $S$ is a stochastic kernel $\pi(d\mid c)$ depending on $c$ only through $S$. Its expected utility under a joint law $\mu$ is $\mathbb E^\pi[U]=\sum_c\mu(c)\sum_d\pi(d\mid c)U(d,c)$. It has regret at most $\delta$ if $\mathbb E^{\pi'}[U]\le\mathbb E^\pi[U]+\delta$ for every policy $\pi'$ with input $S$, and is optimal if $\delta=0$.
--   8. **Policy oracles (Definition 5).** A policy oracle maps a masking $S\subseteq\mathrm{Pa}_D$ and a mixture $w$ of local interventions to a policy. It is $\delta$-optimal if for every $S\subseteq\mathrm{Pa}_D$ and every mixture $w$ it returns a policy with input $S$ and regret at most $\delta$ under $P(\cdot;\sigma_w)$.
--   9. **Domain dependence (Assumption 2).** There are joint laws $P,P'$ that factorise according to the graph such that no policy (with input $\mathrm{Pa}_D$) optimal under $P$ is optimal under $P'$.
--   10. **Context quantities (Appendix C).** For a context $c_0$ on $S$, $P(\mathrm{pa}_D';\sigma)=\sum_{c:c|_S=c_0|_S}\mu(c)$ and $\sum_zP(c;\sigma)U(d,c)=\sum_{c:c|_S=c_0|_S}\mu(c)U(d,c)$, with $Z=C\setminus S$.
--
--   **Formalization Note** The decision has no chance-variable children: the paper's proofs use $\mathrm{Ch}_D=\{U\}$ (Appendix C, proof of Lemma 4), and under Assumption 1 any chance descendant of $D$ is outside $\mathrm{Anc}_U$ and does not affect any expected utility. Assumption 1 then holds automatically. A local intervention acts on all variables at once, as in the proofs of Lemma 3 and Theorem 1. Conditional distributions are written as functions of the whole joint state that depend only on the parents.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Sections 2.1-2.3 (Definitions 1-4, Assumptions 1-2) and Appendices A.1-A.3 (parameterisation, Definition 5), pp. 2-4, 15-18

import Mathlib

/-!
Richens and Everitt, *Robust agents learn causal world models*, ICLR 2024, arXiv:2402.10877v7:
causal Bayesian networks over finitely many categorical chance variables, local, mixed and soft
interventions, single-decision single-utility causal influence diagrams with Assumptions 1 and 2,
policies, regret, policy oracles, and the parameterisation of CIDs used for "almost all CIDs"
(Sections 2.1-2.3 and Appendices A.1-A.3).
-/

open MeasureTheory

noncomputable section

namespace RobustAgentsCausal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} {A : Type*} [Fintype A]

/-- Section 2.1 and Appendix A.2: a joint state `c` of the chance variables `C = {C_i}`, the
variable `C_i` taking the categorical values `0, …, k i - 1`. -/
abbrev Cfg (k : ι → ℕ) := (i : ι) → Fin (k i)

/-- The joint states `c` and `c'` agree on the variables in `S`. -/
def AgreeOn (S : Finset ι) (c c' : Cfg k) : Prop := ∀ i ∈ S, c i = c' i

/-- A function of the joint state depends only on the variables in `S`. -/
def DependsOnlyOn {β : Type*} (S : Finset ι) (f : Cfg k → β) : Prop :=
  ∀ c c' : Cfg k, AgreeOn S c c' → f c = f c'

/-- Appendix A.1: `C_j` is a (proper) ancestor of `C_i` in the graph whose parent sets are `pa`,
i.e. there is a directed path `C_j → ⋯ → C_i` with edges `C_a → C_b` for `a ∈ pa b`. -/
def IsProperAncestor (pa : ι → Finset ι) (j i : ι) : Prop :=
  Relation.TransGen (fun a b => a ∈ pa b) j i

/-- Definition 1: the graph with parent sets `pa` is a directed acyclic graph. -/
def IsAcyclic (pa : ι → Finset ι) : Prop := ∀ i, ¬ IsProperAncestor pa i i

/-- Appendix A.1, Figure 5: the chance variables in `Anc_U`. The utility `U` has the decision `D`
and the chance variables `paU` as parents and the decision has the chance variables `paD` as
parents, so these are the chance variables in `paU ∪ paD` and their ancestors. -/
def ancU (pa : ι → Finset ι) (paD paU : Finset ι) : Set ι :=
  {j | ∃ i ∈ paU ∪ paD, j = i ∨ IsProperAncestor pa j i}

/-- Definition 1: `P i c` is a conditional probability distribution `P(C_i = · ∣ pa_i)` over the
values of `C_i` that depends on the joint state `c` only through the parents `pa i`. -/
def IsCPDAt (pa : ι → Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (i : ι) : Prop :=
  (∀ c v, 0 ≤ P i c v) ∧ (∀ c, ∑ v, P i c v = 1) ∧ DependsOnlyOn (pa i) (P i)

/-- Definition 1: a family of conditional probability distributions for the graph `pa`. -/
def IsCPD (pa : ι → Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ) : Prop :=
  ∀ i, IsCPDAt pa P i

/-- Definition 1: the Markov factorisation `P(c) = ∏_i P(c_i ∣ pa_i)`. -/
def jointProb (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (c : Cfg k) : ℝ := ∏ i, P i c (c i)

/-- Definition 2: a local intervention `do(C_i = f_i(c_i))` on every chance variable at once, as used
in the proofs of Lemma 3 and Theorem 1 (`f_i = id` leaves `C_i` untouched, a constant `f_i` is a
hard intervention). -/
abbrev LocalInt (k : ι → ℕ) := (i : ι) → Fin (k i) → Fin (k i)

/-- Definition 2, eq. (1): the conditional distribution after the local intervention `f`,
`P(c_i ∣ pa_i; σ) = ∑_{c_i' : f_i(c_i') = c_i} P(c_i' ∣ pa_i)`. -/
def localCPD (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (f : LocalInt k) (i : ι) (c : Cfg k)
    (v : Fin (k i)) : ℝ :=
  ∑ v' ∈ Finset.univ.filter (fun v' => f i v' = v), P i c v'

/-- Section 2.1: the joint distribution of the chance variables after the local intervention `f`,
`P(c; σ) = ∏_i P(c_i ∣ pa_i; σ)`. -/
def localJoint (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (f : LocalInt k) (c : Cfg k) : ℝ :=
  ∏ i, localCPD P f i c (c i)

/-- Definition 3: `w` is a mixed intervention `σ* = ∑_f w_f σ_f` over the local interventions
(`w_f ≥ 0`, `∑_f w_f = 1`). -/
def IsMixture (w : LocalInt k → ℝ) : Prop := (∀ f, 0 ≤ w f) ∧ ∑ f, w f = 1

/-- Definition 3: `P(c ∣ σ*) = ∑_f w_f P(c ∣ σ_f)`. -/
def mixJoint (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (w : LocalInt k → ℝ) (c : Cfg k) : ℝ :=
  ∑ f, w f * localJoint P f c

/-- Section 2.1: a soft intervention on the chance variables in `T`, replacing the conditional
distribution of each `C_i`, `i ∈ T`, by `newCPD i`, which depends on a new parent set `newPa i`. -/
structure SoftInt (k : ι → ℕ) where
  /-- The intervened variables. -/
  T : Finset ι
  /-- The new parent sets `Pa*_i`. -/
  newPa : ι → Finset ι
  /-- The new conditional distributions `P'(C_i ∣ Pa*_i)`. -/
  newCPD : (i : ι) → Cfg k → Fin (k i) → ℝ

/-- Section 2.1: the parent sets of the graph after the soft intervention `σ`. -/
def SoftInt.modPa (σ : SoftInt k) (pa : ι → Finset ι) : ι → Finset ι :=
  fun i => if i ∈ σ.T then σ.newPa i else pa i

/-- Section 2.1: `σ` is a soft intervention for the graph `pa`: its new conditional distributions
are conditional distributions for the new parent sets, and no cycle is introduced. -/
def SoftInt.IsCompatible (σ : SoftInt k) (pa : ι → Finset ι) : Prop :=
  (∀ i ∈ σ.T, IsCPDAt σ.newPa σ.newCPD i) ∧ IsAcyclic (σ.modPa pa)

/-- Section 2.1: `P(c; σ) = ∏_{i ∈ T} P'(c_i ∣ pa*_i) ∏_{i ∉ T} P(c_i ∣ pa_i)`. -/
def softJoint (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (σ : SoftInt k) (c : Cfg k) : ℝ :=
  ∏ i, if i ∈ σ.T then σ.newCPD i c (c i) else P i c (c i)

/-- Appendix A.2: a configuration `pa_i` of the parents of `C_i`. -/
abbrev PaCfg (k : ι → ℕ) (pa : ι → Finset ι) (i : ι) := (j : ↥(pa i)) → Fin (k j)

/-- Appendix A.2: the parameters `θ_P = {P(c_i ∣ pa_i) : c_i ∈ {0, …, k_i - 2}}` of the joint
distribution, one real number per variable, parent configuration and non-final state. -/
abbrev CPDParam (k : ι → ℕ) (pa : ι → Finset ι) :=
  ((i : ι) × (PaCfg k pa i × Fin (k i - 1))) → ℝ

/-- Appendix A.2: the parameters `θ_P` define conditional distributions: they are nonnegative and
sum to at most `1` for each variable and parent configuration. -/
def ValidParam (pa : ι → Finset ι) (θ : CPDParam k pa) : Prop :=
  ∀ i (p : PaCfg k pa i),
    (∀ v, 0 ≤ θ ⟨i, (p, v)⟩) ∧ ∑ v : Fin (k i - 1), θ ⟨i, (p, v)⟩ ≤ 1

/-- Appendix A.2: the conditional distributions defined by `θ_P`; the last state receives
`P(C_i = k_i - 1 ∣ pa_i) = 1 - ∑_{c_i ≤ k_i - 2} P(c_i ∣ pa_i)`. -/
def cpdOf (pa : ι → Finset ι) (θ : CPDParam k pa) (i : ι) (c : Cfg k) (v : Fin (k i)) : ℝ :=
  if h : (v : ℕ) + 1 < k i then θ ⟨i, (fun j => c j.1, ⟨v, by omega⟩)⟩
  else 1 - ∑ v' : Fin (k i - 1), θ ⟨i, (fun j => c j.1, v')⟩

/-- Appendix A.2: the parameters `θ_U = {U(d, x)}` of the utility, one real number per decision `d`
and configuration `x` of the chance parents `paU` of `U`. -/
abbrev UParam (k : ι → ℕ) (A : Type*) (paU : Finset ι) := A → ((j : ↥paU) → Fin (k j)) → ℝ

/-- Definition 4: the utility `U(d, x)` as a function of the decision and the joint state. -/
def utilOf (paU : Finset ι) (uθ : UParam k A paU) (d : A) (c : Cfg k) : ℝ :=
  uθ d (fun j => c j.1)

/-- Section 2.2: a (stochastic) policy `π(d ∣ pa_D)` whose input is the chance variables in `S`. -/
def IsPolicy (S : Finset ι) (π : Cfg k → A → ℝ) : Prop :=
  (∀ c d, 0 ≤ π c d) ∧ (∀ c, ∑ d, π c d = 1) ∧ DependsOnlyOn S π

/-- Section 2.2: the expected utility `E^π[U] = ∑_c P(c) ∑_d π(d ∣ pa_D) U(d, c)` of a policy when the
chance variables have joint distribution `μ` (the decision has no chance descendants). -/
def expUtil (μ : Cfg k → ℝ) (u : A → Cfg k → ℝ) (π : Cfg k → A → ℝ) : ℝ :=
  ∑ c, μ c * ∑ d, π c d * u d c

/-- Section 2.2 and Definition 5: `π` has regret at most `δ`, `E^π[U] ≥ E^{π*}[U] - δ`, among the
policies with input `S`. -/
def IsDeltaOptimal (δ : ℝ) (S : Finset ι) (μ : Cfg k → ℝ) (u : A → Cfg k → ℝ)
    (π : Cfg k → A → ℝ) : Prop :=
  IsPolicy S π ∧ ∀ π', IsPolicy S π' → expUtil μ u π' ≤ expUtil μ u π + δ

/-- Section 2.2: `π` is an optimal policy among the policies with input `S`. -/
def IsOptimal (S : Finset ι) (μ : Cfg k → ℝ) (u : A → Cfg k → ℝ) (π : Cfg k → A → ℝ) : Prop :=
  IsDeltaOptimal 0 S μ u π

/-- Definition 5: a policy oracle on the domains `Σ` (mixtures of local interventions together with
a masking `Pa_D' ⊆ Pa_D` of the policy's inputs), returning the policy `π_σ(d ∣ pa_D')`. -/
abbrev Oracle (k : ι → ℕ) (A : Type*) := Finset ι → (LocalInt k → ℝ) → Cfg k → A → ℝ

/-- Definition 5: the policy oracle is `δ`-optimal for the CID with conditional distributions `P`,
utility `u` and decision parents `paD`: for every masking `S ⊆ paD` and mixture `w` of local
interventions it returns a policy with input `S` and regret at most `δ` in `M(σ)`. -/
def IsDeltaOptimalOracle (δ : ℝ) (paD : Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ)
    (u : A → Cfg k → ℝ) (O : Oracle k A) : Prop :=
  ∀ S ⊆ paD, ∀ w : LocalInt k → ℝ, IsMixture w → IsDeltaOptimal δ S (mixJoint P w) u (O S w)

/-- Definition 5: an optimal policy oracle (`δ = 0`). -/
def IsOptimalOracle (paD : Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ)
    (u : A → Cfg k → ℝ) (O : Oracle k A) : Prop :=
  IsDeltaOptimalOracle 0 paD P u O

/-- Assumption 2 (domain dependence): there are joint distributions `P`, `P'` compatible with the
graph `pa` such that no policy optimal under `P` is optimal under `P'`. -/
def DomainDependent (pa : ι → Finset ι) (paD : Finset ι) (u : A → Cfg k → ℝ) : Prop :=
  ∃ P P' : (i : ι) → Cfg k → Fin (k i) → ℝ, IsCPD pa P ∧ IsCPD pa P' ∧
    ∀ π, IsOptimal paD (jointProb P) u π → ¬ IsOptimal paD (jointProb P') u π

open Classical in
/-- Appendix C: the probability `P(Pa_D' = pa_D'; σ) = ∑_z P(C = c; σ)` of the context `c₀` on the
variables `S`, `Z = C ∖ S`, under the joint distribution `μ`. -/
def ctxProb (μ : Cfg k → ℝ) (S : Finset ι) (c₀ : Cfg k) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => AgreeOn S c₀ c), μ c

open Classical in
/-- Appendix C, eqs. (8)-(9): the unnormalised conditional expected utility
`∑_z P(C = c; σ) U(d, c) = P(pa_D'; σ) E[u ∣ pa_D', do(D = d); σ]` of decision `d` in the context
`c₀` on the variables `S`, `Z = C ∖ S`. -/
def ctxUtil (μ : Cfg k → ℝ) (u : A → Cfg k → ℝ) (S : Finset ι) (c₀ : Cfg k) (d : A) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => AgreeOn S c₀ c), μ c * u d c

end RobustAgentsCausal


