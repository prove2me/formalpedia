-- Prove2me | Definitions.Def_MultiCollQ_levelCount
-- name    : MultiCollQ_levelCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:56.639797+00:00
-- url     : https://prove2.me/theorems/4c0602db-9fea-464b-8370-6696673fcc7e
-- title:
--   Public buckets, occupancies $o_b(D)$, level counters $C_j(D)$, amplitudes $a_{j,m}$ and first moments $m_j$
-- statement:
--   Public buckets $Q_1,\dots,Q_h$ partition $[N]$; $b(y)$ is the index of the bucket containing $y$ and $d_c=|Q_c|$. In §3 every bucket has size $1\le d_c\le k$; buckets have **size multiset** $\lambda=(1^{n_1},\dots,k^{n_k})$ if moreover exactly $n_i$ buckets have size $i$.
--
--   For a partial injection $D:[N]\rightharpoonup[N]$ (a database), the **occupancy** of bucket $Q_c$ is $o_c(D)=|\mathrm{im}(D)\cap Q_c|$ and the **level-$j$ counter** is
--
--   $$
--   C_j(D)=\bigl|\{c : o_c(D)\ge j\}\bigr|,
--   $$
--
--   counted over all buckets. For a joint state $\zeta$ of the accessible registers and the database register, with $P_{j,m}=\sum_{D:C_j(D)\ge m}|D\rangle\langle D|$ and $\widehat C_j=\sum_D C_j(D)|D\rangle\langle D|$,
--
--   $$
--   a_{j,m}=\|P_{j,m}\zeta\|,\qquad m_j=\langle\zeta,\widehat C_j\zeta\rangle .
--   $$
--
--   These quantities measure how many buckets the database has filled to level $j$; the lower bound tracks their growth query by query.
--
--   **Formalization Note** Buckets are a map `b : Fin N → Fin h`. A database is `CompPermOracle.PartialPerm N = PEquiv (Fin N) (Fin N)`. Both operators are diagonal in the basis $|c,D\rangle$, so $a_{j,m}$ is defined as $(\sum_c\sum_{D:C_j(D)\ge m}|\zeta(c,D)|^2)^{1/2}$ and $m_j$ as $\sum_c\sum_D C_j(D)|\zeta(c,D)|^2$.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), §2.4, pp.13–15; §3, pp.18–19; §3.2, p.23

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm

namespace MultiCollQ

open CompPermOracle

/-- The size `d_b = |Q_b|` of the public bucket `Q_b` (Peng, Hou, Dong, manuscript (Oct. 2026),
§2.4, p.13; §3, p.18).

**Formalization Note.** The buckets `Q_1, …, Q_h` partitioning `[N]` are given by the map
`b : Fin N → Fin h`, `y ↦` the index of the bucket containing `y` (the paper's `b(y)`, p.13);
`Q_c = b⁻¹(c)`. Indices are 0-based. -/
def bucketSize {N h : ℕ} (b : Fin N → Fin h) (c : Fin h) : ℕ :=
  (Finset.univ.filter fun y => b y = c).card

/-- Public buckets of sizes in `[1, k]`: the setting of §3 (Peng, Hou, Dong, manuscript
(Oct. 2026), §3, p.18: "Partition `[N]` into public buckets `Q_1, …, Q_h`, and write
`d_b = |Q_b| ≤ k`").

**Formalization Note.** The blocks of a partition are nonempty, hence `1 ≤ d_b`. -/
def BucketsBounded {N h : ℕ} (b : Fin N → Fin h) (k : ℕ) : Prop :=
  ∀ c, 1 ≤ bucketSize b c ∧ bucketSize b c ≤ k

/-- Public buckets with size multiset `λ = (1^{n_1}, …, k^{n_k})`: every bucket has size in
`[1, k]` and exactly `n_i` buckets have size `i` (Peng, Hou, Dong, manuscript (Oct. 2026), §2.4,
p.13: "public buckets `Q_1, …, Q_h` partitioning `[N]` with size multiset `λ`").

**Formalization Note.** Then automatically `N = Σ i n_i` and `h = Σ n_i`. -/
def HasBucketType {N h : ℕ} (b : Fin N → Fin h) (k : ℕ) (n : ℕ → ℕ) : Prop :=
  BucketsBounded b k ∧ ∀ i, 1 ≤ i → i ≤ k → (Finset.univ.filter fun c => bucketSize b c = i).card = n i

/-- The occupancy `o_c(D) = |im(D) ∩ Q_c|` of bucket `Q_c` in the database `D` (Peng, Hou, Dong,
manuscript (Oct. 2026), §3, p.19). -/
def occ {N h : ℕ} (b : Fin N → Fin h) (D : PartialPerm N) (c : Fin h) : ℕ :=
  (Finset.univ.filter fun y => ¬ NotInIm D y ∧ b y = c).card

/-- The level-`j` counter `C_j(D) = |{c : o_c(D) ≥ j}|`, the number of buckets holding at least `j`
recorded images (Peng, Hou, Dong, manuscript (Oct. 2026), §2.4, p.14 (for `j = r`); §3, p.19).
It ranges over the full set of buckets. -/
def levelCount {N h : ℕ} (b : Fin N → Fin h) (j : ℕ) (D : PartialPerm N) : ℕ :=
  (Finset.univ.filter fun c => j ≤ occ b D c).card

/-- The database amplitude `a_{j,m} = ‖P_{j,m} ζ‖` of a joint state `ζ` on (accessible registers)
⊗ (database register `L`), where `P_{j,m} = Σ_{D : C_j(D) ≥ m} |D⟩⟨D|` (with the identity on the
accessible registers) (Peng, Hou, Dong, manuscript (Oct. 2026), §2.4, pp.14–15; §3, p.19).

**Formalization Note.** `P_{j,m}` is diagonal in the computational basis `|c, D⟩`, so
`‖P_{j,m} ζ‖ = (Σ_c Σ_{D : C_j(D) ≥ m} |ζ(c, D)|²)^{1/2}`; this sum is the definition. `m = 0`
gives `‖ζ‖`. -/
noncomputable def dbAmp {C : Type} [Fintype C] {N h : ℕ} (b : Fin N → Fin h) (j m : ℕ)
    (ζ : Hil (C × PartialPerm N)) : ℝ :=
  Real.sqrt (∑ c, ∑ D ∈ Finset.univ.filter (fun D : PartialPerm N => m ≤ levelCount b j D),
    ‖ζ (c, D)‖ ^ 2)

/-- The first moment `m_j = ⟨ζ, Ĉ_j ζ⟩` of the counting operator `Ĉ_j = Σ_D C_j(D)|D⟩⟨D|` in the
joint state `ζ` (Peng, Hou, Dong, manuscript (Oct. 2026), §3.2, p.23).

**Formalization Note.** `Ĉ_j` is diagonal in the basis `|c, D⟩`, so
`⟨ζ, Ĉ_j ζ⟩ = Σ_c Σ_D C_j(D) |ζ(c, D)|²`; this sum is the definition. -/
noncomputable def firstMoment {C : Type} [Fintype C] {N h : ℕ} (b : Fin N → Fin h) (j : ℕ)
    (ζ : Hil (C × PartialPerm N)) : ℝ :=
  ∑ c, ∑ D : PartialPerm N, (levelCount b j D : ℝ) * ‖ζ (c, D)‖ ^ 2

end MultiCollQ


