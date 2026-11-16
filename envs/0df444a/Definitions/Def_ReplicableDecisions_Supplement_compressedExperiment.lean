-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_compressedExperiment
-- name    : ReplicableDecisions_Supplement_compressedExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:04:19.821734+00:00
-- url     : https://prove2.me/theorems/8d2e7a98-967a-4bfd-a7f0-772d6a77fc94
-- title:
--   Channels, image laws $PK$ and the compressed experiment $\mathcal E_K=(\mathcal Q,\Gamma_K)$
-- statement:
--   A **channel** $K$ from $\mathcal Z$ to a finite set $\mathcal W$ assigns to every $z$ a probability vector $K(z,\cdot)$ on $\mathcal W$; the image of a law is $(PK)(w)=\sum_zP(z)K(z,w)$. For a finite experiment $\mathcal E=(\mathcal P,\Gamma)$ put
--   $$\mathcal Q=\{PK:P\in\mathcal P\},\qquad \Gamma_K(Q)=\bigcap_{P\in\mathcal P:\,PK=Q}\Gamma(P),\qquad \mathcal E_K=(\mathcal Q,\Gamma_K).$$
--   $K$ is **admissible** if every $\Gamma_K(Q)$ is nonempty.
--
--   The compressed experiment has $M_K=|\mathcal Q|$ models; Theorem 6.12 shows when it has the same optimal sample size and chain scales as $\mathcal E$.
--
--   **Formalization Note** $\mathcal E_K$ is indexed by the image set $\mathcal Q$ itself, so its models are distinct and $M_K=|\mathcal Q|$.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), §6.4, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment

namespace ReplicableDecisions.Supplement

/-- **A channel** `K` from `Z` to `W`: every row `K(z, ·)` is a probability vector on `W`. Chen,
*Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), §6.4, p.35
(PDF p.37). -/
def IsChannel {Z W : Type} [Fintype W] (K : Z → W → ℝ) : Prop :=
  ∀ z, K z ∈ stdSimplex ℝ W

/-- **The image law** `PK(w) = ∑_z P(z) K(z, w)`. Chen, STOC 2027 submission (sha256 52d181db…),
§6.4, p.35 (PDF p.37). -/
noncomputable def pushforward {Z W : Type} [Fintype Z] (P : Z → ℝ) (K : Z → W → ℝ) : W → ℝ :=
  fun w => ∑ z, P z * K z w

theorem pushforward_mem_simplex {Z W : Type} [Fintype Z] [Fintype W] {P : Z → ℝ}
    {K : Z → W → ℝ} (hP : P ∈ stdSimplex ℝ Z) (hK : IsChannel K) :
    pushforward P K ∈ stdSimplex ℝ W := by
  refine ⟨fun w => Finset.sum_nonneg fun z _ => mul_nonneg (hP.1 z) ((hK z).1 w), ?_⟩
  unfold pushforward
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hK _).2, mul_one]
  exact hP.2

/-- **The image family** `Q = {PK : P ∈ P}`. Chen, STOC 2027 submission (sha256 52d181db…), §6.4,
p.35 (PDF p.37). -/
def channelImage {ι : Type*} {Z W : Type} [Fintype Z] (E : Experiment ι Z) (K : Z → W → ℝ) :
    Set (W → ℝ) :=
  Set.range fun i => pushforward (E.P i) K

/-- The image family of a finite family is finite; `M_K = |Q|` is its cardinality. -/
noncomputable instance channelImage.instFintype {ι : Type*} [Finite ι] {Z W : Type} [Fintype Z]
    (E : Experiment ι Z) (K : Z → W → ℝ) : Fintype (channelImage E K) :=
  (Set.finite_range fun i => pushforward (E.P i) K).fintype

/-- **The compressed experiment** `E_K = (Q, Γ_K)`, models part. Chen, STOC 2027 submission
(sha256 52d181db…), §6.4, p.35 (PDF p.37).

**Formalization Note.** `E_K` is indexed by the image set `Q` itself, so its models are distinct
and `M_K = |Q|`; it is not indexed by the original models. -/
noncomputable def compressedExperiment {ι : Type*} {Z W : Type} [Fintype Z] [Fintype W]
    (E : Experiment ι Z) (K : Z → W → ℝ) (hK : IsChannel K) :
    Experiment (channelImage E K) W where
  P := fun q => q.1
  mem_simplex := fun q => by
    obtain ⟨i, hi⟩ := q.2
    rw [← hi]
    exact pushforward_mem_simplex (E.mem_simplex i) hK
  distinct := Subtype.val_injective

/-- **The compressed acceptable sets** `Γ_K(Q) = ⋂_{P∈P: PK=Q} Γ(P)`. Chen, STOC 2027 submission
(sha256 52d181db…), §6.4, p.35 (PDF p.37). -/
def compressedΓ {ι : Type*} {Z W : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (K : Z → W → ℝ) (Γ : ι → Set Y) (q : channelImage E K) : Set Y :=
  ⋂ i ∈ {i | pushforward (E.P i) K = q.1}, Γ i

/-- **Admissibility of `K`:** "every Γ_K(Q) is nonempty". Chen, STOC 2027 submission
(sha256 52d181db…), §6.4, p.35 (PDF p.37). -/
def IsAdmissible {ι : Type*} {Z W : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (K : Z → W → ℝ) (Γ : ι → Set Y) : Prop :=
  ∀ q, (compressedΓ E K Γ q).Nonempty

end ReplicableDecisions.Supplement


