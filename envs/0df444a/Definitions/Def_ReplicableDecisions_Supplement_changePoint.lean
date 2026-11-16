-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_changePoint
-- name    : ReplicableDecisions_Supplement_changePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:01:35.152195+00:00
-- url     : https://prove2.me/theorems/ef6f6866-7761-4d6b-a533-c64aa206982d
-- title:
--   Change-point experiment (4.1): $d+1$ product Bernoulli laws on $\{0,1\}^d$
-- statement:
--   Fix an integer $d\ge1$ and $0<c\le1/4$, and put $a=c/\sqrt d$. The observation space is $\mathcal Z=\{0,1\}^d$. For $j\in\{0,\dots,d\}$, $P_j$ is the product law whose first $j$ coordinates have law $\mathrm{Ber}(1/2+a)$ and whose remaining coordinates have law $\mathrm{Ber}(1/2-a)$; the acceptable sets are the early/late sets of (4.1). There are $M=d+1$ models, and one sample is one whole vector in $\{0,1\}^d$.
--
--   The task is to distinguish an early change from a late one while replicating at every intermediate position; Theorems 4.2 and 4.4 give its weak and strong sample complexities.
--
--   **Formalization Note** It is the ordered product experiment with $Q_i^-=\mathrm{Ber}(1/2-a)$ and $Q_i^+=\mathrm{Ber}(1/2+a)$ on every block; $\mathrm{Ber}(p)$ gives $1=$ `true` probability $p$. The hypotheses $d\ge1$, $0<c\le1/4$ are needed to prove that the models are distinct probability vectors.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), (4.1), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ReplicableDecisions_Supplement_orderedProductExperiment

namespace ReplicableDecisions.Supplement

/-- **The Bernoulli law** `Ber(p)` on `{0, 1}`, with `1 = true` of probability `p`. Chen,
*Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), (4.1), p.16
(PDF p.18). -/
noncomputable def ber (p : ℝ) : Bool → ℝ := fun b => if b then p else 1 - p

theorem ber_mem_simplex {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ber p ∈ stdSimplex ℝ Bool := by
  refine ⟨fun b => ?_, ?_⟩
  · cases b <;> simp [ber] <;> linarith
  · simp [ber]

/-- **The bias** `a = c/√d` of the change-point experiment. Chen, STOC 2027 submission
(sha256 52d181db…), (4.1), p.16 (PDF p.18): "Fix an integer d ≥ 1 and 0 < c ≤ 1/4, and put
a = c/√d." -/
noncomputable def cpBias (d : ℕ) (c : ℝ) : ℝ := c / Real.sqrt d

theorem cpBias_pos {d : ℕ} {c : ℝ} (hd : 1 ≤ d) (hc₀ : 0 < c) : 0 < cpBias d c := by
  unfold cpBias
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem cpBias_le {d : ℕ} {c : ℝ} (hd : 1 ≤ d) (hc₀ : 0 < c) (hc : c ≤ 1 / 4) :
    cpBias d c ≤ 1 / 4 := by
  unfold cpBias
  have h1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The change-point experiment (4.1).** Chen, STOC 2027 submission (sha256 52d181db…), (4.1),
p.16 (PDF p.18): "The observation space is Z = {0, 1}^d. For j ∈ {0, . . . , d}, let P_j be the
product distribution whose first j coordinates have law Ber(1/2 + a) and whose remaining
coordinates have law Ber(1/2 − a)." There are `M = d + 1` models; one sample is one whole vector.

**Formalization Note.** It is the ordered product experiment with `Q⁻_i = Ber(1/2 − a)` and
`Q⁺_i = Ber(1/2 + a)` on every block; coordinate `i : Fin d` (0-based) has law `Ber(1/2 + a)`
under `P_j` iff `i < j`. The acceptable sets are `earlyLateΓ d`. The hypotheses `d ≥ 1`,
`0 < c ≤ 1/4` are those of (4.1) and are needed to prove that the models are distinct
probability vectors. -/
noncomputable def changePoint (d : ℕ) (c : ℝ) (hd : 1 ≤ d) (hc₀ : 0 < c) (hc : c ≤ 1 / 4) :
    Experiment (Fin (d + 1)) (Fin d → Bool) :=
  orderedProductExperiment (Zs := fun _ => Bool) (fun _ => ber (1 / 2 - cpBias d c))
    (fun _ => ber (1 / 2 + cpBias d c))
    (fun _ => ber_mem_simplex (by linarith [cpBias_le hd hc₀ hc]) (by linarith [cpBias_pos hd hc₀]))
    (fun _ => ber_mem_simplex (by linarith [cpBias_pos hd hc₀]) (by linarith [cpBias_le hd hc₀ hc]))
    (fun _ b => by
      have h1 := cpBias_pos hd hc₀
      have h2 := cpBias_le hd hc₀ hc
      cases b <;> simp [ber] <;> linarith)
    (fun _ h => by
      have h1 := cpBias_pos hd hc₀
      have := congrFun h true
      simp [ber] at this
      linarith)

end ReplicableDecisions.Supplement


