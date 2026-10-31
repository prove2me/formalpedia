-- Prove2me | Definitions.Def_SimpleMechMRF_MRF
-- name    : SimpleMechMRF_MRF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:18.312042+00:00
-- url     : https://prove2.me/theorems/9add1e1d-cd84-4508-b1b5-8412d0a72beb
-- title:
--   Markov random field over a hypergraph with local potentials, its law $D$ and maximum weighted degree $\Delta$
-- statement:
--   A **Markov random field** (MRF) over a hypergraph $G=([n],E)$ consists of a finite nonempty alphabet $\Sigma_i=T_i\subset\mathbb R_{\ge0}$ for each item $i$, a vertex potential $\psi_i:\Sigma_i\to\mathbb R$, and for each hyperedge $e\in E$ ($e\subseteq[n]$) a potential $\psi_e:\Sigma_e\to\mathbb R$, $\Sigma_e=\times_{v\in e}\Sigma_v$, which depends only on the coordinates $x_e=(x_v)_{v\in e}$. Its law $D$ on $\times_{i}\Sigma_i$ is
--
--   $$
--   D(c)\;\propto\;\prod_{v\in[n]}e^{\psi_v(c_v)}\prod_{e\in E}e^{\psi_e(c_e)}.
--   $$
--
--   The **weighted degree** of item $i$ and the **maximum weighted degree** are
--
--   $$
--   d_i=\max_{x\in\times_{\ell\in[n]}T_\ell}\Big|\sum_{e\in E:\,i\in e}\psi_e(x_e)\Big|,\qquad \Delta=\max_{i\in[n]}d_i .
--   $$
--
--   When $E=\emptyset$ the law is a product measure and $\Delta=0$; $\Delta$ measures how far the item values are from independent, and every bound of the mission degrades as $e^{O(\Delta)}$.
--
--   **Formalization Note** A hyperedge potential is a function of the whole configuration together with a locality field ($\psi_e(x)=\psi_e(y)$ whenever $x_e=y_e$); without locality any full-support distribution would be an MRF. The law has full support $T=\times_i T_i$. $\Delta$ is computed from the given potentials, not minimized over representations; for $n=0$ it is $0$.
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Definition 2 (p.7, PDF 8), Definition 4 (p.7, PDF 8), and 'Throughout the paper, when we say the type distribution D is a MRF …' (p.7)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist

open scoped NNReal

namespace SimpleMechMRF

/-- **A Markov random field over a hypergraph `([n], E)` with finite nonnegative alphabets.**
Vertex `i` (item `i`) carries the alphabet `A i` (finite and nonempty, the set `Tᵢ = Σᵢ` of values
of item `i`) and a vertex potential `ψv i : ℝ≥0 → ℝ`. Each hyperedge `e ∈ E` (a subset of the
items) carries a hyperedge potential `ψe e`, which is a function of the configuration `x` that
**depends only on the coordinates `x_e = (x i)_{i ∈ e}`** (field `ψe_local`).

Cai & Oikonomou, *On Simple Mechanisms for Dependent Items*, arXiv:2106.10814v2, Definition 2
(Markov Random Fields), p. 7 (PDF 8): "Associated with every vertex v ∈ V is a random variable
Xv taking values in some alphabet Σv, as well as a potential function ψv : Σv → R. Associated
with every hyperedge e ⊆ V is a potential function ψe : Σe → R."

**Formalization Note.** `ψe e` is typed on all configurations `Fin n → ℝ≥0`; the locality field
makes it a function on `Σ_e = ×_{v∈e} Σ_v`, as in the paper. Without locality every
full-support distribution would be an MRF with one hyperedge. The alphabets are finite sets of
nonnegative reals (reading: item values are nonnegative and the type space is finite). Only the
values of `ψv i` on `A i` and of `ψe e` on configurations in `×ᵢ A i` matter. -/
structure MRF (n : ℕ) where
  /-- The alphabet `Σᵢ = Tᵢ` of item `i`. -/
  A : Fin n → Finset ℝ≥0
  A_nonempty : ∀ i, (A i).Nonempty
  /-- Vertex potentials `ψᵢ`. -/
  ψv : Fin n → ℝ≥0 → ℝ
  /-- The hyperedges `E` of the hypergraph on `[n]`. -/
  E : Finset (Finset (Fin n))
  /-- Hyperedge potentials `ψ_e`. -/
  ψe : Finset (Fin n) → (Fin n → ℝ≥0) → ℝ
  ψe_local : ∀ e x y, (∀ i ∈ e, x i = y i) → ψe e x = ψe e y

namespace MRF

variable {n : ℕ}

/-- The configuration space `×_{i∈[n]} Σᵢ`. -/
noncomputable def configs (G : MRF n) : Finset (Fin n → ℝ≥0) :=
  Fintype.piFinset G.A

theorem configs_nonempty (G : MRF n) : G.configs.Nonempty :=
  Fintype.piFinset_nonempty.mpr G.A_nonempty

/-- The unnormalized weight `Πᵢ e^{ψᵢ(xᵢ)} Π_{e∈E} e^{ψ_e(x_e)}`. -/
noncomputable def weight (G : MRF n) (x : Fin n → ℝ≥0) : ℝ :=
  Real.exp (∑ i, G.ψv i (x i) + ∑ e ∈ G.E, G.ψe e x)

/-- The partition function `Σ_{x ∈ ×ᵢ Σᵢ} weight x`. -/
noncomputable def partition (G : MRF n) : ℝ :=
  ∑ x ∈ G.configs, G.weight x

theorem partition_pos (G : MRF n) : 0 < G.partition :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) G.configs_nonempty

/-- **The law `D` of the MRF**: `π(c) ∝ Π_{v} e^{ψ_v(c_v)} Π_{e∈E} e^{ψ_e(c_e)}` on
`×_{v} Σ_v` (Definition 2, p. 7). It has full support, so `T = ×ᵢ Tᵢ`. -/
noncomputable def law (G : MRF n) : TypeDist n where
  supp := G.configs
  pmf x := G.weight x / G.partition
  pmf_pos := fun _ _ => div_pos (Real.exp_pos _) G.partition_pos
  sum_pmf := by rw [← Finset.sum_div]; exact div_self G.partition_pos.ne'

/-- **Weighted degree** `dᵢ(t) = max_{x ∈ ×_{ℓ∈[n]} T_ℓ} |Σ_{e∈E : i∈e} ψ_e(x_e)|`
(Definition 4, p. 7, PDF 8), as a nonnegative real (`Real.nnabs` is the absolute value). -/
noncomputable def weightedDegree (G : MRF n) (i : Fin n) : ℝ≥0 :=
  G.configs.sup fun x => Real.nnabs (∑ e ∈ G.E.filter (fun e => i ∈ e), G.ψe e x)

/-- **Maximum weighted degree** `Δ(t) = max_{i∈[n]} dᵢ(t)` (Definition 4, p. 7, PDF 8).

**Formalization Note.** The maximum is taken in `ℝ≥0` and cast to `ℝ`; for `n = 0` it is `0`.
`Δ` is computed from the given potentials (not minimized over representations of the law). -/
noncomputable def maxWeightedDegree (G : MRF n) : ℝ :=
  ((Finset.univ : Finset (Fin n)).sup fun i => G.weightedDegree i : ℝ≥0)

end MRF

end SimpleMechMRF


