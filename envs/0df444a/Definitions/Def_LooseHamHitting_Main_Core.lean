-- Prove2me | Definitions.Def_LooseHamHitting_Main_Core
-- name    : LooseHamHitting_Main_Core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:02.436687+00:00
-- url     : https://prove2.me/theorems/881e5c2f-79b0-45e3-bc7d-3835985e7364
-- title:
--   Ω(n, m, ℓ), admissible and near-critical triples, Assumption 4.2, K and Φ(H), the edge-deletion laws P, P∗, β, q_e, L_j, A_j, σ², j₀, and D_Z(G, ℓ)
-- statement:
--   **Definition 4.1.** $\Omega(n,m,\ell)=\{F\subseteq\binom{[n]}3:|F|=m,\ d_F(v)\ge\ell_v\ \forall v\in[n]\}$. $(n,m,\ell)$ is **admissible** if $\Omega(n,m,\ell)\ne\emptyset$, and **near-critical** if $|m-n\log n/3|\le n\log\log n$ and $|\ell_v-\lfloor0.01\log n\rfloor|\le2$ for every $v$.
--
--   **Assumption 4.2.** $(n_*,m_*,\ell)$ is admissible and near-critical; $M_0$ is a matching on $[n_*]$ of $s$ pairs with $1\le s\le n_*^{1/10}$ and $n_*+s$ even; $F_*$ is uniform on $\Omega(n_*,m_*,\ell)$. $K=\{e\in\binom{[n_*]}3:|e\cap V(M_0)|\le1\}$ and $\Phi(H)=\Phi(H\cap K,M_0)$.
--
--   **§8 deletion laws.** $P$ is the law of the process $\binom{[n_*]}3=H_{N}\supsetneq\dots\supsetneq H_{m_*}$, $N=\binom{n_*}3$, deleting a uniform edge at each step; $P_*=P[\,\cdot\mid H_{m_*}\in\Omega(n_*,m_*,\ell)]$; $\beta=|\Omega(n_*,m_*,\ell)|/\binom{N}{m_*}$. For $\Phi(H)>0$ and $e\in H$, $q_e(H)$ is the fraction of the cycles counted by $\Phi(H)$ that contain $e$. With $\log0=-\infty$,
--   $$L_j=\log\Phi\Big(\binom{[n_*]}3\Big)-\frac{n_*-s}2\sum_{h=j+1}^{N}\frac1h,\qquad A_j=\Big\{\log\Phi(H_j)\ge L_j-\frac{n_*}{\sqrt{\log n_*}}\Big\},$$
--   $$\sigma^2=\frac{C_0^2(n_*-s)^2}4\sum_{j=m_*+1}^{N}\frac1{j^2}.$$
--   $j_0$ is the size of the first state $H_j$ ($j=N,N-1,\dots,m_*+1$) with $\Phi(H_j)=0$ or $\max_{e\in H_j}q_e(H_j)>C_0(n_*-s)/(2j)$, and $j_0=m_*$ if there is none. For Lemma 7.4: $B_*=\{v:d_{F}(v)\le0.03\log n\}$ and $D_Z(G,\ell)=\sum_{v\in V\setminus Z}\max\{0,\ell_v-d_{G-Z}(v)\}$.
--
--   **Formalization Note.** The deletion process is encoded by a uniform ordering $\sigma$ of the triples with $H_j$ its first $j$ triples (the edge deleted from $H_j$ is the $j$-th triple, uniform in $H_j$ given the later states). $P_*[E]$ is a conditional counting probability. $A_j$ is encoded as $\Phi(H_j)>0$ and $\log\Phi(H_j)\ge L_j-n_*/\sqrt{\log n_*}$, which is the $\log0=-\infty$ convention whenever $\Phi(\binom{[n_*]}3)>0$ (all large $n_*$, Lemma 3.3). `Real.log` is natural.
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 13 (Definition 4.1, Assumption 4.2); p. 28 (D_Z); pp. 30–31 (§8: P, P∗, β, q_e, (8.1), A_j, σ², j₀)

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process

set_option autoImplicit false

/-!
# The conditioned core (§4) and the edge-deletion laws (§8)

León, Liu, arXiv:2610.29894v1, p. 13 (Definition 4.1, Assumption 4.2), p. 28 (`D_Z`),
pp. 30–31 (`P`, `P∗`, `β`, `q_e`, `L_j`, `A_j`, `σ²`, `j₀`).

The deletion process `\binom{[n]}{3} = H_N ⊋ ⋯ ⊋ H_m` deleting a uniform edge at each step is
encoded by a uniform ordering `σ` of the triples with `H_j` its first `j` triples (the edge deleted
from `H_j` is the `j`-th triple). Its law is `P`.
-/

namespace LooseHamHitting.Main

noncomputable section

open Classical

/-- `Ω(n, m, ℓ) := {F ⊆ \binom{[n]}{3} : |F| = m, d_F(v) ≥ ℓ_v ∀ v ∈ [n]}`. -/
def Omega (n m : ℕ) (ℓ : Fin n → ℕ) : Finset (Finset (Finset (Fin n))) :=
  OmegaV (Finset.univ : Finset (Fin n)) m ℓ

/-- `(n, m, ℓ)` is admissible: `Ω(n, m, ℓ) ≠ ∅`. -/
def Admissible (n m : ℕ) (ℓ : Fin n → ℕ) : Prop :=
  (Omega n m ℓ).Nonempty

/-- `(n, m, ℓ)` is near-critical: `|m − n log n/3| ≤ n log log n` and
`|ℓ_v − ⌊0.01 log n⌋| ≤ 2` for every `v`. -/
def NearCritical (n m : ℕ) (ℓ : Fin n → ℕ) : Prop :=
  |(m : ℝ) - (n : ℝ) * Real.log n / 3| ≤ (n : ℝ) * Real.log (Real.log n) ∧
    ∀ v, |(ℓ v : ℤ) - ⌊(0.01 : ℝ) * Real.log n⌋| ≤ 2

/-- Probability of an event under the uniform law on a finite set `S`. -/
def uniformProb {β : Type*} (S : Finset β) (E : β → Prop) : ℝ :=
  ((S.filter E).card : ℝ) / (S.card : ℝ)

/-- Assumption 4.2(i)–(ii): `(n∗, m∗, ℓ)` admissible and near-critical; `M₀` a matching on
`[n∗]` of `s` pairs with `1 ≤ s ≤ n∗^{1/10}` and `n∗ + s` even. (Item (iii), `F∗ ∼ Unif Ω`, is
the law used in the statements.) -/
def CoreAssumption (n m : ℕ) (ℓ : Fin n → ℕ) (M₀ : Finset (Finset (Fin n))) : Prop :=
  Admissible n m ℓ ∧ NearCritical n m ℓ ∧ IsMatching Finset.univ M₀ ∧ 1 ≤ M₀.card ∧
    (M₀.card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) ∧ Even (n + M₀.card)

/-- `K := {e ∈ \binom{[n]}{3} : |e ∩ V(M₀)| ≤ 1}`. -/
def coreK (n : ℕ) (M₀ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  compatibleTriples Finset.univ M₀

/-- `Φ(H) := Φ(H ∩ K, M₀)` on the vertex set `[n]`. -/
def PhiCore (n : ℕ) (M₀ : Finset (Finset (Fin n))) (H : Finset (Finset (Fin n))) : ℕ :=
  Phi Finset.univ (H ∩ coreK n M₀) M₀

/-- The complete 3-graph `\binom{[n]}{3}`. -/
def completeGraph (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

/-- `q_e(H)`: the fraction of the cycles counted by `Φ(H)` that contain `e`. -/
def edgeMarginal (n : ℕ) (M₀ : Finset (Finset (Fin n))) (H : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : ℝ :=
  (((mixedHamCycles Finset.univ (H ∩ coreK n M₀) M₀).filter (fun C => e ∈ C)).card : ℝ) /
    (PhiCore n M₀ H : ℝ)

/-- `L_j := log Φ(\binom{[n]}{3}) − ((n − s)/2) ∑_{h=j+1}^{\binom{n}{3}} 1/h` (8.1). -/
def Lref (n : ℕ) (M₀ : Finset (Finset (Fin n))) (j : ℕ) : ℝ :=
  Real.log (PhiCore n M₀ (completeGraph n)) -
    ((n : ℝ) - M₀.card) / 2 * ∑ h ∈ Finset.Icc (j + 1) (Nat.choose n 3), (1 : ℝ) / h

/-- `A_j := {log Φ(H_j) ≥ L_j − n/√(log n)}` with `log 0 = −∞` (so `Φ(H_j) = 0` fails it). -/
def EventA (n : ℕ) (M₀ : Finset (Finset (Fin n))) (σ : Ordering n) (j : ℕ) : Prop :=
  0 < PhiCore n M₀ (prefixGraph σ j) ∧
    Lref n M₀ j - (n : ℝ) / Real.sqrt (Real.log n) ≤ Real.log (PhiCore n M₀ (prefixGraph σ j))

/-- The edge-marginal bound `max_{e ∈ H} q_e(H) ≤ C₀ (n − s)/(2j)` fails at `H`. -/
def MarginalExceeds (C₀ : ℝ) (n : ℕ) (M₀ : Finset (Finset (Fin n)))
    (H : Finset (Finset (Fin n))) (j : ℕ) : Prop :=
  ∃ e ∈ H, C₀ * ((n : ℝ) - M₀.card) / (2 * j) < edgeMarginal n M₀ H e

/-- `σ² := C₀² (n − s)²/4 · ∑_{j=m+1}^{\binom{n}{3}} 1/j²`. -/
def sigmaSq (C₀ : ℝ) (n m s : ℕ) : ℝ :=
  C₀ ^ 2 * ((n : ℝ) - s) ^ 2 / 4 * ∑ j ∈ Finset.Icc (m + 1) (Nat.choose n 3), (1 : ℝ) / (j : ℝ) ^ 2

/-- The stopping rule inspected at `H_j` before deleting from it. -/
def StopAt (C₀ : ℝ) (n : ℕ) (M₀ : Finset (Finset (Fin n))) (H : Finset (Finset (Fin n)))
    (j : ℕ) : Prop :=
  PhiCore n M₀ H = 0 ∨ (0 < PhiCore n M₀ H ∧ MarginalExceeds C₀ n M₀ H j)

/-- `j₀`: the size of the first state `H_j` (scanning `j = \binom{n}{3}, …, m + 1`) at which the
rule stops, and `m` if it never stops before `H_m`. -/
def stopSize (C₀ : ℝ) (n m : ℕ) (M₀ : Finset (Finset (Fin n))) (σ : Ordering n) : ℕ :=
  max m (((Finset.Icc (m + 1) (Nat.choose n 3)).filter
    (fun j => StopAt C₀ n M₀ (prefixGraph σ j) j)).sup id)

/-- `P∗[E]`: the deletion law `P` conditioned on `H_m ∈ Ω(n, m, ℓ)`. -/
def condProbCore (n m : ℕ) (ℓ : Fin n → ℕ) (E : Ordering n → Prop) : ℝ :=
  condProbOrd n E (fun σ => prefixGraph σ m ∈ Omega n m ℓ)

/-- `β := |Ω(n, m, ℓ)| / \binom{\binom{n}{3}}{m}`. -/
def betaCore (n m : ℕ) (ℓ : Fin n → ℕ) : ℝ :=
  ((Omega n m ℓ).card : ℝ) / (Nat.choose (Nat.choose n 3) m : ℝ)

/-- `B∗ := {v : d_F(v) ≤ 0.03 log n}` (Lemma 7.4). -/
def lowDegreeSet (n : ℕ) (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (degree F v : ℝ) ≤ 0.03 * Real.log n)

/-- `D_Z(G, ℓ) := ∑_{v ∈ V \ Z} max{0, ℓ_v − d_{G−Z}(v)}` (p. 28). -/
def deficit {α : Type*} (V : Finset α) (G : Finset (Finset α)) (ℓ : α → ℕ) (Z : Finset α) : ℤ :=
  ∑ v ∈ V \ Z, max 0 ((ℓ v : ℤ) - degree (deleteVerts G Z) v)

end

end LooseHamHitting.Main


