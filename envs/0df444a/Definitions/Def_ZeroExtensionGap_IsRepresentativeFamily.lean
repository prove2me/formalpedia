-- Prove2me | Definitions.Def_ZeroExtensionGap_IsRepresentativeFamily
-- name    : ZeroExtensionGap_IsRepresentativeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:09.648466+00:00
-- url     : https://prove2.me/theorems/fdb00faf-ee4f-493e-a8b9-cfab88a0d51d
-- title:
--   Cloud representatives, radii and errors of §6
-- statement:
--   Fix a labelling $f:V(X)\to V(X)$ and $0<\tau\le\tau_0$. The radii are $r_1:=0$ and $r_i:=r_{i-1}+\tau\sigma_i$. A vertex $x$ of an $i$-cloud $C$ is **bad** for $C$ if $d_X(f(x),z_C)>r_i$. $e_C$ is the fraction of bad vertices, and $e_i$ is the average of $e_C$ over the $i$-clouds. $L_n:=(t-1)\lceil n^{0.99}\rceil/n$.
--
--   **The representatives** $z_C$ are built in increasing order of cloud size. On a 1-cloud, $z_C$ is a most frequent label. For an $i$-cloud $C$ with $2\le i\le t$ and children $C_u$ with representatives $z_u$, take the $\tau\sigma_i$-bounded random partition $P$ of $Z_C=\{z_u\}$ with $\Pr[P(z_u)\ne P(z_v)]\le K\,d_X(z_u,z_v)/\sigma_{i-1}$ (Lemma 11); take a realization $P_C$ of it with $q_C(P_C)\le\mathbb E[q_C(P)]$, where $q_C$ counts the edges of $H$ whose child representatives are separated; take a part $B$ of $P_C$ with $I_B=\{u:z_u\in B\}$ largest; and set $z_C:=z_{u^*}$ for some $u^*\in I_B$.
--
--   **Formalization Note.** `IsRepresentativeFamily` records exactly this. Every choice the page leaves free is free here, and every fact the page fixes is a clause. A family is indexed by clouds as sets of vertices.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §6.1–§6.2, pp.29–30 (PDF pp.31–32)

import Mathlib
import Definitions.Def_ZeroExtensionGap_gapInstance
import Definitions.Def_ZeroExtensionGap_RandomPartition

open scoped ENNReal

namespace ZeroExtensionGap

variable {n : ℕ}

/-- The radii `r_1 := 0`, `r_i := r_{i-1} + τσ_i`, p.29 (PDF p.31) (Chen, Zhu, *Almost Tight Hardness of
Approximation for 0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…). -/
noncomputable def radius (t n : ℕ) (τ : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.Icc 2 i, τ * sigma t n j

/-- `L_n := (t-1)⌈n^{0.99}⌉/n`, p.30 (PDF p.32). -/
noncomputable def Ln (t n : ℕ) : ℝ := ((t : ℝ) - 1) * (⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ : ℝ) / (n : ℝ)

open Classical in
/-- The number of vertices of `C` with label `ℓ`. -/
noncomputable def labelCount {W : Type*} (f : W → W) (C : Finset W) (ℓ : W) : ℕ :=
  (C.filter fun x => f x = ℓ).card

section Fixed

variable (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n) (τ K : ℝ)
  (f : TowerV n (t - 1) → TowerV n (t - 1)) (z : Finset (TowerV n (t - 1)) → TowerV n (t - 1))

/-- `Z_C := {z_u : u ∈ V(H)}`, the representatives of the children of `C`, p.29 (PDF p.31). -/
noncomputable def childReps (i : ℕ) (C : Finset (TowerV n (t - 1))) : Finset (TowerV n (t - 1)) :=
  Finset.univ.image fun a : Fin n => z (childOf t i C a)

open Classical in
/-- `q_C(Q)`, the number of edges `{u,v} ∈ E(H)` with `Q(z_u) ≠ Q(z_v)`, p.30 (PDF p.32). -/
noncomputable def crossingCount (i : ℕ) (C : Finset (TowerV n (t - 1)))
    (Q : Finpartition (childReps t z i C)) : ℕ :=
  ((edgeFin H).filter fun e =>
    Q.part (z (childOf t i C (edgeTail e))) ≠ Q.part (z (childOf t i C (edgeHead e)))).card

open Classical in
/-- `I_B := {u ∈ V(H) : z_u ∈ B}`, p.30 (PDF p.32). -/
noncomputable def childGroup (i : ℕ) (C : Finset (TowerV n (t - 1)))
    (B : Finset (TowerV n (t - 1))) : Finset (Fin n) :=
  Finset.univ.filter fun a => z (childOf t i C a) ∈ B

/-- The construction of a parent representative in §6.2, pp.29–30 (PDF pp.31–32), for an `i`-cloud `C`,
`2 ≤ i ≤ t`: a `τσ_i`-bounded random partition `P` of `Z_C`, with respect to `d_X`, with
`Pr[P(z_u) ≠ P(z_v)] ≤ K d_X(z_u, z_v)/σ_{i-1}` (the partition of Lemma 11, `K` its constant); a
`τσ_i`-bounded realization `Q` with `q_C(Q) ≤ E[q_C(P)]`; a part `B` with `I_B` largest; and `z_C := z_{u*}`
for some `u* ∈ I_B`. -/
def IsParentRep (i : ℕ) (C : Finset (TowerV n (t - 1))) : Prop :=
  ∃ P : PMF (Finpartition (childReps t z i C)),
    IsBoundedRandomPartition (towerDist t H g φ (t - 1)) (τ * sigma t n i) P ∧
    (∀ x ∈ childReps t z i C, ∀ y ∈ childReps t z i C,
      separationProb P x y ≤ K * (towerDist t H g φ (t - 1) x y).toReal / sigma t n (i - 1)) ∧
    ∃ Q ∈ P.support,
      ((crossingCount t H z i C Q : ℕ) : ℝ≥0∞) ≤
        ∑' Q', P Q' * ((crossingCount t H z i C Q' : ℕ) : ℝ≥0∞) ∧
      ∃ B ∈ Q.parts,
        (∀ B' ∈ Q.parts, (childGroup t z i C B').card ≤ (childGroup t z i C B).card) ∧
        ∃ a ∈ childGroup t z i C B, z C = z (childOf t i C a)

/-- The representatives "constructed above" in §6.1–§6.2, pp.29–30 (PDF pp.31–32): `z_C` is a most
frequent label on each 1-cloud, and on each `i`-cloud, `2 ≤ i ≤ t`, it comes from the construction
`IsParentRep`. The choices the page leaves free (a most frequent label, the partition, its realization,
the largest group, `u*`) are free here too. -/
structure IsRepresentativeFamily : Prop where
  base : ∀ C, IsCloud t 1 C → ∀ ℓ, labelCount f C ℓ ≤ labelCount f C (z C)
  step : ∀ i, 2 ≤ i → i ≤ t → ∀ C, IsCloud t i C → IsParentRep t H g φ τ K z i C

open Classical in
/-- `e_C`, the fraction of vertices of the `i`-cloud `C` that are bad for `C`, that is, with
`d_X(f(x), z_C) > r_i` (p.29, PDF p.31). -/
noncomputable def cloudError (i : ℕ) (C : Finset (TowerV n (t - 1))) : ℝ :=
  ((C.filter fun x => ENNReal.ofReal (radius t n τ i) <
      towerDist t H g φ (t - 1) (f x) (z C)).card : ℝ) / (C.card : ℝ)

/-- `e_i := |C_i|⁻¹ ∑_{C ∈ C_i} e_C`, the average error at level `i` (p.29, PDF p.31). -/
noncomputable def levelError (i : ℕ) : ℝ :=
  (∑ C ∈ cloudsAt (n := n) t i, cloudError t H g φ τ f z i C) / ((cloudsAt (n := n) t i).card : ℝ)

end Fixed

end ZeroExtensionGap


