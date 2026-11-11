-- Prove2me | Definitions.Def_RandModSubsetSum_TagJoin
-- name    : RandModSubsetSum_TagJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:20.552989+00:00
-- url     : https://prove2.me/theorems/7bd2198a-730d-42b1-8360-21d24728c99b
-- title:
--   An abstract model of one join: coordinate partitions, tag trials and the retained-pair event
-- statement:
--   This module models one join $(j,v)$ of RepresentationSearch (§4.3) independently of the input lists. The data are strata of sizes $n_r$, $N_{\rm blk}$ blocks, subblock lengths $m_{r,h}$, the full-stratum sibling counts $n_r\hat\Gamma^{(r)}_{j,v}$, subblock sibling counts $m_{r,h}\hat\Gamma_{r,h}$, and tag joint counts $m_{r,h}\hat C_{r,h}(a,b,s)$, consistent with each other. With $n=\sum_rn_r$:
--
--   1. (17) $p^{\rm part}_{j,v}=\prod_r\prod_h|T_{m_{r,h}}(\hat\Gamma_{r,h})|/|T_{n_r}(\hat\Gamma^{(r)}_{j,v})|$ and (18) $\nu_{j,v}=\lceil n^2/p^{\rm part}_{j,v}\rceil$;
--   2. (19)–(20) $p^{\rm tag}_h=\prod_r p^{\rm tag}_{r,h}$ with $p^{\rm tag}_{r,h}=\prod_{a,b}\binom{m\hat\Gamma(a,b)}{(m\hat C(a,b,s))_s}\Big/\binom{m}{(m\hat C_S(s))_s}$, and $T_h=\lceil n^2/p^{\rm tag}_h\rceil$.
--
--   The randomness is uniform on the set of samples consisting of $\nu$ coordinate partitions with the prescribed subblock lengths and, for every partition, block $h$ and sequence of trial indices $(i_1,\dots,i_h)$, a tag word whose restriction to each subblock lies in $T_{m_{r,h}}(\hat C_S)$: independent uniform partitions and fresh, independent, uniform tags for every trial of every branch (TagFilter, Algorithm 5).
--
--   For a fixed sibling pair $(u,v)$, the event **Retained** holds when some partition passes both subblock marginal tests (Algorithm 1, lines 16–17) and some sequence of trials $i_h\le T_h$ passes, at every block and on every subblock, both marginal tag tests: $(u[J],s)$ has type $\hat C_{AS}$ and $(v[J],s)$ has type $\hat C_{BS}$. Since a branch continues while both of its lists are nonempty, this is the event that both words occur in a common pair of lists emitted by TagFilter.
--
--   **Formalization Note** Strata, symbol alphabet, tag alphabet and $N_{\rm blk}$ are arbitrary (the paper has 13 strata, $N_{\rm blk}=64$ and 40 tags). Trial sequences are padded with zeros after block $h$; tags at unused indices are never consulted.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), §3.2, pp. 14–16; §4.3, (17)–(20), pp. 26–27; Algorithms 1 and 5, pp. 18, 61; preassigned tags, p. 34

import Mathlib
import Definitions.Def_RandModSubsetSum_Types

open scoped BigOperators

namespace RandModSubsetSum

/-- The prescribed data of one join `(j, v)` of RepresentationSearch (§4.3, pp. 26–27), in a form
that does not depend on the input lists: strata `r ∈ ι` of sizes `n_r`; `N_blk` blocks; subblock
lengths `m_{r,h}`; the full-stratum sibling counts `n_r Γ̂^{(r)}_{j,v}(a, b)` (`G`); the subblock
sibling counts `m_{r,h} Γ̂_{r,h}(a, b)` (`Gb`); and the subblock tag joint counts
`m_{r,h} Ĉ_{r,h}(a, b, s)` over the tag alphabet `S` (`Ct`).
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), §4.3, pp. 26–27. -/
structure JoinData (ι α S : Type) where
  Nb : ℕ
  nr : ι → ℕ
  m : ι → Fin Nb → ℕ
  G : ι → α × α → ℕ
  Gb : ι → Fin Nb → α × α → ℕ
  Ct : ι → Fin Nb → α × α × S → ℕ

namespace JoinData

variable {ι α S : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype S]

/-- Consistency of the prescribed counts (§4.3, p. 26): the subblock lengths sum to `n_r`; each
subblock type has `m_{r,h}` entries; the subblock counts of each sibling pair sum over blocks to its
full-stratum count; and the tag joint counts have sibling marginal `Gb`. -/
def Consistent (J : JoinData ι α S) : Prop :=
  (∀ r, ∑ h, J.m r h = J.nr r) ∧
  (∀ r h, ∑ ab, J.Gb r h ab = J.m r h) ∧
  (∀ r ab, ∑ h, J.Gb r h ab = J.G r ab) ∧
  (∀ r h ab, ∑ s, J.Ct r h (ab.1, ab.2, s) = J.Gb r h ab)

/-- The word length `n = Σ_r n_r`. -/
def len (J : JoinData ι α S) : ℕ := ∑ r, J.nr r

/-- The tag marginal counts `m_{r,h} Ĉ_S(s) = Σ_{a,b} m_{r,h} Ĉ(a, b, s)`. -/
def CtS (J : JoinData ι α S) (r : ι) (h : Fin J.Nb) (s : S) : ℕ :=
  ∑ ab : α × α, J.Ct r h (ab.1, ab.2, s)

/-- (17), p. 26: `p^part_{j,v} = Π_r Π_h |T_{m_{r,h}}(Γ̂_{r,h})| / |T_{n_r}(Γ̂^{(r)}_{j,v})|`, the type
class sizes written as multinomial coefficients. -/
noncomputable def pPart (J : JoinData ι α S) : ℝ :=
  ∏ r, (∏ h, multinom (J.m r h) (J.Gb r h)) / multinom (J.nr r) (J.G r)

/-- (19)–(20), p. 27: `p^tag_h = Π_r p^tag_{r,h}` with
`p^tag_{r,h} = Π_{a,b} (m Γ̂(a,b) choose (m Ĉ(a,b,s))_s) / (m choose (m Ĉ_S(s))_s)`. -/
noncomputable def pTag (J : JoinData ι α S) (h : Fin J.Nb) : ℝ :=
  ∏ r, (∏ ab : α × α, multinom (J.Gb r h ab) (fun s => J.Ct r h (ab.1, ab.2, s))) /
    multinom (J.m r h) (J.CtS r h)

/-- (18), p. 26: the number of coordinate partitions `ν_{j,v} = ⌈n² / p^part_{j,v}⌉`. -/
noncomputable def nu (J : JoinData ι α S) : ℕ := ⌈((J.len : ℝ) ^ 2) / J.pPart⌉₊

/-- (20), p. 27: the number of tag trials at each branch entering block `B_h`,
`T_h = ⌈n² / p^tag_h⌉`. -/
noncomputable def trials (J : JoinData ι α S) (h : Fin J.Nb) : ℕ := ⌈((J.len : ℝ) ^ 2) / J.pTag h⌉₊

/-- A common bound on trial indices, `max_h T_h + 1`. -/
noncomputable def Tmax (J : JoinData ι α S) : ℕ := Finset.univ.sup J.trials + 1

/-- A coordinate partition of every stratum into `N_blk` blocks: `blk r k = h` puts coordinate `k`
of stratum `r` into the subblock `J_{r,h}`. -/
abbrev Partition (J : JoinData ι α S) := (r : ι) → Fin (J.nr r) → Fin J.Nb

open Classical in
/-- The partition has the prescribed subblock lengths `|J_{r,h}| = m_{r,h}` (Algorithm 1, line 15). -/
def IsPartition (J : JoinData ι α S) (blk : J.Partition) : Prop :=
  ∀ r h, (Finset.univ.filter (fun k => blk r k = h)).card = J.m r h

/-- The sequence of trial indices `(i_1, …, i_h)` padded with zeros after block `h`. -/
def pad (J : JoinData ι α S) (h : Fin J.Nb) (σ : Fin J.Nb → Fin J.Tmax) : Fin J.Nb → Fin J.Tmax :=
  fun h' => if h' ≤ h then σ h' else ⟨0, Nat.succ_pos _⟩

/-- A sample of all random choices at the join: `ν` coordinate partitions and, for every partition
`k`, block `h` and sequence of trial indices `(i_1, …, i_h)` (padded), a tag word on every stratum. -/
abbrev Sample (J : JoinData ι α S) :=
  (Fin J.nu → J.Partition) ×
    (Fin J.nu → Fin J.Nb → (Fin J.Nb → Fin J.Tmax) → (r : ι) → Fin (J.nr r) → S)

noncomputable instance instFintypeSample (J : JoinData ι α S) : Fintype J.Sample :=
  @instFintypeProd _ _ (inferInstance : Fintype (Fin J.nu → J.Partition))
    (inferInstance : Fintype (Fin J.nu → Fin J.Nb → (Fin J.Nb → Fin J.Tmax) → (r : ι) →
      Fin (J.nr r) → S))

open Classical in
/-- The support of the join's randomness: every partition has the prescribed subblock lengths, and
every tag word, on the subblock `J_{r,h}` of its partition, lies in the type class `T_m(Ĉ_S)` (and is
a fixed default symbol elsewhere). The model is the uniform distribution on this set: independent
uniform partitions (independent across strata), and, given them, independent tag words uniform in
their type classes, one for every partition, block and sequence of trial indices — fresh tags for
every trial of every branch, as in TagFilter (Algorithm 5; Figure 2, p. 16). -/
noncomputable def space [Inhabited S] (J : JoinData ι α S) : Finset J.Sample :=
  Finset.univ.filter (fun ω =>
    (∀ k, J.IsPartition (ω.1 k)) ∧
    ∀ k h pre r,
      (∀ s, (Finset.univ.filter (fun c => ω.1 k r c = h ∧ ω.2 k h pre r c = s)).card = J.CtS r h s) ∧
      (∀ c, ω.1 k r c ≠ h → ω.2 k h pre r c = default))

open Classical in
/-- The path event of Lemma 4.6 for the fixed sibling pair `(u, v)`: some partition `k` retains
both words by the subblock marginal tests of Algorithm 1 (lines 16–17), and some sequence of trial
indices `i_h < T_h` passes, at every block `h` and on every subblock `J_{r,h}`, both marginal tag
tests of TagFilter (Algorithm 5): `(u[J], s)` has type `Ĉ_{AS}` and `(v[J], s)` has type `Ĉ_{BS}`.
Since a branch continues while both of its lists are nonempty, this is exactly the event that both
words occur in a common pair of lists emitted by TagFilter. -/
def Retained (J : JoinData ι α S) (u v : (r : ι) → Fin (J.nr r) → α) (ω : J.Sample) : Prop :=
  ∃ k : Fin J.nu,
    (∀ r h a, (Finset.univ.filter (fun c => ω.1 k r c = h ∧ u r c = a)).card =
        ∑ b, J.Gb r h (a, b)) ∧
    (∀ r h b, (Finset.univ.filter (fun c => ω.1 k r c = h ∧ v r c = b)).card =
        ∑ a, J.Gb r h (a, b)) ∧
    ∃ σ : Fin J.Nb → Fin J.Tmax, (∀ h, (σ h).val < J.trials h) ∧
      ∀ h r,
        (∀ a s, (Finset.univ.filter (fun c =>
            ω.1 k r c = h ∧ u r c = a ∧ ω.2 k h (J.pad h σ) r c = s)).card =
          ∑ b, J.Ct r h (a, b, s)) ∧
        (∀ b s, (Finset.univ.filter (fun c =>
            ω.1 k r c = h ∧ v r c = b ∧ ω.2 k h (J.pad h σ) r c = s)).card =
          ∑ a, J.Ct r h (a, b, s))

open Classical in
/-- Probability of `Retained` under the uniform distribution on `space`. -/
noncomputable def retainProb [Inhabited S] (J : JoinData ι α S) (u v : (r : ι) → Fin (J.nr r) → α) :
    ℝ :=
  ((J.space.filter (J.Retained u v)).card : ℝ) / (J.space.card : ℝ)

end JoinData

end RandModSubsetSum


