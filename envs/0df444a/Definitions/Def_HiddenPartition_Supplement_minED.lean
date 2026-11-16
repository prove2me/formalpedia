-- Prove2me | Definitions.Def_HiddenPartition_Supplement_minED
-- name    : HiddenPartition_Supplement_minED
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:59:27.861214+00:00
-- url     : https://prove2.me/theorems/2a882b07-e32f-48a1-bf8c-46c7cfb12af1
-- title:
--   Densest-$q$-Partition objectives MinED, MinPD, SumED, SumPD and the optimum $f^*_q(G)$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $q\ge1$. A **$q$-partition** $\mathcal P=\{P_1,\dots,P_q\}$ of $V$ is a partition of all of $V$ into $q$ pairwise disjoint **nonempty** parts; it is **balanced** if $|P_1|=\dots=|P_q|$. The four density objectives are
--
--   1. $\mathrm{MinED}_G(\mathcal P)=\min_{i\in[q]}\mathrm{ED}_G(P_i)$;
--   2. $\mathrm{MinPD}_G(\mathcal P)=\min_{i\in[q]}\mathrm{PD}_G(P_i)$;
--   3. $\mathrm{SumED}_G(\mathcal P)=\sum_{i\in[q]}\mathrm{ED}_G(P_i)$;
--   4. $\mathrm{SumPD}_G(\mathcal P)=\sum_{i\in[q]}\mathrm{PD}_G(P_i)$.
--
--   For each objective $f$, the optimum is
--
--   $$
--   f^*_q(G)=\max_{\mathcal P:\,P_1\cup\dots\cup P_q=V} f_G(\mathcal P),
--   $$
--
--   the maximum over all $q$-partitions of $V$ into nonempty parts.
--
--   Densest-$q$-Partition asks for a $q$-partition maximizing one of these objectives; these definitions are shared by all hardness and algorithmic results of the mission.
--
--   **Formalization Note** A $q$-partition is a surjective labelling $P:V\to\{0,\dots,q-1\}$, with parts $P^{-1}(i)$. Minimum and maximum are the real $\inf$/$\sup$ over finite sets, hence true minima and maxima in the paper's range $1\le q\le|V|$ (Lean returns $0$ on an empty index set, a case no statement uses).
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §2.1, p.10 (pdf p.12)

import Mathlib
import Definitions.Def_HiddenPartition_Supplement_edgeDensity

set_option autoImplicit false

namespace HiddenPartition.Supplement

/-- **The parts of a labelling** (Agrawal et al., STOC 2027 submission, manuscript sha256
17239d0b…, §2.1, p.10 (pdf p.12)). A `q`-partition `P = {P_1, …, P_q}` of `V` is written as a
labelling `P : V → Fin q`; `part P i` is the part `P_{i+1} = P⁻¹(i)`.

**Formalization Note.** Parts are indexed `0, …, q-1`. -/
def part {V : Type*} [Fintype V] {q : ℕ} (P : V → Fin q) (i : Fin q) : Finset V :=
  Finset.univ.filter (fun v => P v = i)

/-- **MinED objective** (Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…,
§2.1 item 1, p.10 (pdf p.12)): `MinED_G(P) = min_{i ∈ [q]} ED_G(P_i)`.

**Formalization Note.** The minimum over the finite index `Fin q` is the real `⨅`; it is a true
minimum for `q ≥ 1`, the only case the mission uses (all parameters satisfy `1 ≤ q ≤ |V(G)|`). -/
noncomputable def minED {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (P : V → Fin q) : ℝ :=
  ⨅ i : Fin q, edgeDensity G (part P i)

/-- **MinPD objective** (§2.1 item 2, p.10 (pdf p.12)): `MinPD_G(P) = min_{i ∈ [q]} PD_G(P_i)`.
Same conventions as `minED`. -/
noncomputable def minPD {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (P : V → Fin q) : ℝ :=
  ⨅ i : Fin q, pairDensity G (part P i)

/-- **SumED objective** (§2.1 item 3, p.10 (pdf p.12)): `SumED_G(P) = Σ_{i ∈ [q]} ED_G(P_i)`. -/
noncomputable def sumED {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (P : V → Fin q) : ℝ :=
  ∑ i : Fin q, edgeDensity G (part P i)

/-- **SumPD objective** (§2.1 item 4, p.10 (pdf p.12)): `SumPD_G(P) = Σ_{i ∈ [q]} PD_G(P_i)`. -/
noncomputable def sumPD {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (P : V → Fin q) : ℝ :=
  ∑ i : Fin q, pairDensity G (part P i)

/-- **Optimum value over all `q`-partitions** (§2.1, p.10 (pdf p.12)):
`f*_q(G) = max_{P : P_1 ∪ ⋯ ∪ P_q = V} f_G(P)`, the maximum over partitions of `V` into `q`
pairwise disjoint **nonempty** parts.

**Formalization Note.** A partition into `q` nonempty parts is a surjective labelling
`V → Fin q`. The supremum is the real `⨆` over this finite set, hence a true maximum whenever the
set is nonempty, i.e. for `1 ≤ q ≤ |V|` (the paper's standing range; on an empty set Lean's value
is `0`, never used). -/
noncomputable def optimum {V : Type*} (q : ℕ) (f : (V → Fin q) → ℝ) : ℝ :=
  ⨆ P : {P : V → Fin q // Function.Surjective P}, f P.1

/-- **Balanced `q`-partition** (§2.1, p.10 (pdf p.12)): a `q`-partition into nonempty parts with
`|P_1| = ⋯ = |P_q|`. -/
def IsBalanced {V : Type*} [Fintype V] {q : ℕ} (P : V → Fin q) : Prop :=
  Function.Surjective P ∧ ∀ i j : Fin q, (part P i).card = (part P j).card

end HiddenPartition.Supplement


