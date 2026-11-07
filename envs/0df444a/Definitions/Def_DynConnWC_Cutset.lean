-- Prove2me | Definitions.Def_DynConnWC_Cutset
-- name    : DynConnWC_Cutset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:15.808122+00:00
-- url     : https://prove2.me/theorems/3eaea859-1d48-439d-86fa-be4bc5a1ecd9
-- title:
--   The $k$-wise cutset structure: identifiers, sampling labels, fingerprints and search
-- statement:
--   Let $\ell=\lceil\log_2 n\rceil$, $B=2^\ell$ and $J=2\ell$. A potential edge $\{u,v\}$ with $u<v$ has the **identifier** $\mathrm{id}=Bu+v+1$. An integer $z$ with $1\le z<2^J$ **decodes** to $\{u,v\}$ when $u=\lfloor(z-1)/B\rfloor$ and $v=(z-1)\bmod B$ satisfy $u<v<n$.
--
--   One instance has random choices $c_0,\dots,c_{k-1},\alpha$, independent and uniform in $\mathbb F_{2^w}$. The **sampling label** of $e$ is the lowest $J$ bits of $H(\mathrm{id}(e))$, where $H(Z)=\sum_{a<k}c_aZ^a$, and threshold $j\in\{0,\dots,J\}$ **selects** $e$ when the lowest $j$ bits of its label are zero. For a vertex set $T$, let $C_{T,j}$ be the selected edges of $\delta_G(T)$, with
--   $$Z_j(T)=\bigoplus_{e\in C_{T,j}}\mathrm{id}(e),\qquad P_j(T)=\sum_{e\in C_{T,j}}\alpha^{\mathrm{id}(e)}.$$
--   **search**$(T)$ examines the thresholds $j=J,J-1,\dots,0$ in turn. It accepts the pair $\{u,v\}$ decoded from $Z_j(T)$ if exactly one of $u,v$ lies in $T$ and $P_j(T)=\alpha^{\mathrm{id}(\{u,v\})}$, and it returns the first accepted pair, or $\bot$ if none is accepted. The dictionary version also requires the pair to be a current graph edge, and may omit the fingerprint test.
--
--   **Formalization Note** $\mathbb F_{2^w}$ is `GaloisField 2 w`, with a fixed bijection `enc` to $w$-bit strings; the paper's polynomial basis is one such bijection. $Z_j$ and $P_j$ are computed directly from the cut, which Appendix A.2 shows equal the sums of the stored vertex summaries over the tree. `KWiseUniform` is the hypothesis of Lemma 11's general clause: the labels of any at most $k$ distinct potential edges are independent and uniform.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Definition 4, p.5 (PDF 6); Appendix A.2, pp.28–29 (PDF 29–30); Remark 26, p.25 (PDF 26)

import Mathlib
import Definitions.Def_DynConnWC_Forest

set_option autoImplicit false

namespace DynConnWC

/-! # The k-wise cutset data structure: identifiers, labels, fingerprints, search

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), Definition 4, p.5, and Appendix A.2, pp.28–29. "Let
ℓ = ⌈log₂ n⌉, B = 2^ℓ, J = 2ℓ. For a potential edge e = {u, v} with u < v, set id(e) = Bu + v + 1.
… An integer z with 1 ≤ z < 2^J decodes to a pair if u = ⌊(z −1)/B⌋ and v = (z −1) mod B satisfy
0 ≤ u < v < n; the pair is {u, v}." "Each instance chooses a random sampling polynomial
H(Z) = Σ_{a=0}^{k−1} c_a Z^a, c_0, …, c_{k−1} independent and uniform in F, and the sampling label
of e is the lowest J bits of H(id(e))." "threshold j ∈ {0, . . . , J} selects e if the lowest j
bits of its label are zero." "Independently of H, each instance chooses a uniform α ∈ F, its
fingerprint base. The fingerprint of e is α^{id(e)}." "For a tree T, let C_{T,j} be the set of
cut edges of T selected at threshold j. Summing the stored values over the vertices of T gives
Z_j(T) = ⊕_{e∈C_{T,j}} id(e), P_j(T) = Σ_{e∈C_{T,j}} α^{id(e)}." "To perform search(T), examine
the thresholds j = J, J −1, . . . , 0 in turn. If Z_j(T) does not decode to a pair, which includes
the case Z_j(T) = 0, skip threshold j. Otherwise let {u, v} be the pair that Z_j(T) decodes to,
and accept it if exactly one of u and v lies in T and P_j(T) = α^{id({u,v})}. Return the first
accepted pair. If no threshold accepts, return ⊥." Remark 26, p.25 (dictionary version): "require
every decoded candidate of every search to be a current graph edge, in addition to the existing
tests."

**Formalization Note.** The field `F_{2^w}` is `GaloisField 2 w`, identified with `w`-bit strings
by a fixed bijection `enc` (the paper's polynomial basis modulo a fixed irreducible polynomial is
one such bijection; nothing below depends on which). An integer identifier is a field element via
`enc.symm (BitVec.ofNat w ·)`. The random choices of one instance (`Coins w k`) are the `k`
coefficients of `H` and the base `α`; their law is uniform on `Coins w k`, i.e. all `k + 1` field
elements are independent and uniform. `⊥` is `none`. `Z_j` and `P_j` are computed directly from
the cut `δ_G(T)`; Appendix A.2 shows that the tree sums of the vertex summaries equal these cut
sums, so the search depends on `T` only through its vertex set and its cut. The search takes the
current graph `G` and a vertex set `T`; the flag `dict` adds the dictionary test of Remark 26.
The **fingerprint test** at a threshold whose value `Z_j` decodes to a pair is `P_j = α^{Z_j}`;
it is defined on any edge set, so it applies both to the cut of a tree and to a cut in `K_t`
(Lemma 21). `KWiseUniform` is the hypothesis of the generalized Lemma 11: the labels of any at
most `k` distinct potential edges are independent and uniform `J`-bit strings. -/

variable {n : ℕ}

/-- Which tests a search applies besides the endpoint test: Appendix A.2's fingerprint test (`plain`),
the fingerprint test and the dictionary test of Remark 26 (`dict`), the dictionary test alone
(`dictNoFp`). -/
inductive SearchMode where
  | plain
  | dict
  | dictNoFp
  deriving DecidableEq

/-- `ℓ = ⌈log₂ n⌉`. -/
def ell (n : ℕ) : ℕ := Nat.clog 2 n

/-- `B = 2^ℓ`. -/
def Bpow (n : ℕ) : ℕ := 2 ^ ell n

/-- `J = 2ℓ`, the bit length of a sampling label. -/
def Jbits (n : ℕ) : ℕ := 2 * ell n

/-- The finite field `F_{2^w}` as a finite type. -/
noncomputable instance gfFintype (w : ℕ) : Fintype (GaloisField 2 w) := Fintype.ofFinite _

/-- The identifier `id({u, v}) = B·min(u,v) + max(u,v) + 1` of a potential edge. -/
def edgeId : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun u v => Bpow n * (min u v).val + (max u v).val + 1, by
    intro a b; simp [min_comm, max_comm]⟩

/-- Decoding: `z` with `1 ≤ z < 2^J` decodes to `{u, v}` when `u = ⌊(z−1)/B⌋` and
`v = (z−1) mod B` satisfy `u < v < n`. -/
def decode (z : ℕ) : Option (Sym2 (Fin n)) :=
  if h : 1 ≤ z ∧ z < 2 ^ Jbits n ∧ (z - 1) / Bpow n < (z - 1) % Bpow n ∧ (z - 1) % Bpow n < n then
    some s(⟨(z - 1) / Bpow n, h.2.2.1.trans h.2.2.2⟩, ⟨(z - 1) % Bpow n, h.2.2.2⟩)
  else none

/-- The random choices of one cutset instance: the coefficients `c_0, …, c_{k-1}` of the sampling
polynomial and the fingerprint base `α`. -/
abbrev Coins (w k : ℕ) := (Fin k → GaloisField 2 w) × GaloisField 2 w

/-- The uniform law on the random choices of one instance. -/
noncomputable def coinLaw (w k : ℕ) : PMF (Coins w k) := PMF.uniformOfFintype (Coins w k)

/-- An integer, written as a `w`-bit string, viewed as a field element. -/
def fieldOfNat {w : ℕ} (enc : GaloisField 2 w ≃ BitVec w) (x : ℕ) : GaloisField 2 w :=
  enc.symm (BitVec.ofNat w x)

/-- The sampling polynomial `H(Z) = Σ_{a<k} c_a Z^a`. -/
noncomputable def sampPoly {w k : ℕ} (c : Fin k → GaloisField 2 w) (z : GaloisField 2 w) :
    GaloisField 2 w :=
  ∑ a : Fin k, c a * z ^ (a : ℕ)

/-- The sampling label of `e`: the lowest `J` bits of `H(id(e))`, as a number below `2^J`. -/
noncomputable def label {w k : ℕ} (enc : GaloisField 2 w ≃ BitVec w)
    (c : Fin k → GaloisField 2 w) (e : Sym2 (Fin n)) : ℕ :=
  (enc (sampPoly c (fieldOfNat enc (edgeId e)))).toNat % 2 ^ Jbits n

/-- Threshold `j` selects `e`: the lowest `j` bits of its label are zero. -/
def Selected {w k : ℕ} (enc : GaloisField 2 w ≃ BitVec w) (c : Fin k → GaloisField 2 w)
    (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  label enc c e % 2 ^ j = 0

open Classical in
/-- The edges of `C` selected at threshold `j` (for `C = δ_G(T)` this is `C_{T,j}`). -/
noncomputable def selCut {w k : ℕ} (enc : GaloisField 2 w ≃ BitVec w)
    (c : Fin k → GaloisField 2 w) (C : Finset (Sym2 (Fin n))) (j : ℕ) : Finset (Sym2 (Fin n)) :=
  C.filter (Selected enc c j)

/-- `⊕_{e∈C} id(e)`, the bitwise XOR of the identifiers. -/
def xorIds (C : Finset (Sym2 (Fin n))) : ℕ := C.fold (· ^^^ ·) 0 edgeId

/-- `Σ_{e∈C} α^{id(e)}`, the field sum of the fingerprints. -/
noncomputable def fpSum {w : ℕ} (α : GaloisField 2 w) (C : Finset (Sym2 (Fin n))) :
    GaloisField 2 w :=
  ∑ e ∈ C, α ^ edgeId e

/-- The fingerprint test on the edge set `C` at threshold `j` passes: `Z_j` decodes to a pair and
`P_j = α^{Z_j}`. -/
def FingerprintPasses {w k : ℕ} (enc : GaloisField 2 w ≃ BitVec w) (co : Coins w k)
    (C : Finset (Sym2 (Fin n))) (j : ℕ) : Prop :=
  ∃ p : Sym2 (Fin n), decode (xorIds (selCut enc co.1 C j)) = some p ∧
    fpSum co.2 (selCut enc co.1 C j) = co.2 ^ xorIds (selCut enc co.1 C j)

/-- The fingerprint test on `C` at threshold `j` is sound: if it passes, the edges of `C`
selected at `j` consist of the decoded edge alone. -/
def FingerprintSound {w k : ℕ} (enc : GaloisField 2 w ≃ BitVec w) (co : Coins w k)
    (C : Finset (Sym2 (Fin n))) (j : ℕ) : Prop :=
  ∀ p : Sym2 (Fin n), decode (xorIds (selCut enc co.1 C j)) = some p →
    fpSum co.2 (selCut enc co.1 C j) = co.2 ^ xorIds (selCut enc co.1 C j) →
    selCut enc co.1 C j = {p}

open Classical in
/-- The pair accepted at threshold `j` by the search of `T` in graph `G`, if any. -/
noncomputable def acceptAt {w k : ℕ} (mode : SearchMode) (enc : GaloisField 2 w ≃ BitVec w)
    (co : Coins w k) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (j : ℕ) :
    Option (Sym2 (Fin n)) :=
  let C := selCut enc co.1 (cutset G T) j
  match decode (n := n) (xorIds C) with
  | none => none
  | some p =>
    if Leaves T p ∧ (mode ≠ .dictNoFp → fpSum co.2 C = co.2 ^ xorIds C) ∧
        (mode ≠ .plain → p ∈ G.edgeSet) then some p
    else none

/-- **search(T)** (Appendix A.2): the first pair accepted at thresholds `J, J − 1, …, 0`, or
`none` (`⊥`). In the dictionary modes a candidate must also be a current graph edge (Remark 26). -/
noncomputable def search {w k : ℕ} (mode : SearchMode) (enc : GaloisField 2 w ≃ BitVec w)
    (co : Coins w k) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Option (Sym2 (Fin n)) :=
  (List.range (Jbits n + 1)).reverse.findSome? (acceptAt mode enc co G T)

open Classical in
/-- Some threshold `j ∈ {0, …, J}` selects exactly one edge of `C`, for the label map `lab`. -/
def SomeThresholdSelectsOne (lab : Sym2 (Fin n) → ℕ) (C : Finset (Sym2 (Fin n))) : Prop :=
  ∃ j ≤ Jbits n, (C.filter (fun e => lab e % 2 ^ j = 0)).card = 1

/-- The labels drawn from `μ` are `k`-wise independent and uniform: for any at most `k` distinct
potential edges (pairs of distinct vertices), their labels are independent and uniform `J`-bit
strings. -/
def KWiseUniform (k : ℕ) (μ : PMF (Sym2 (Fin n) → Fin (2 ^ Jbits n))) : Prop :=
  ∀ S : Finset (Sym2 (Fin n)), S.card ≤ k → (∀ e ∈ S, ¬ e.IsDiag) →
    ∀ f : Sym2 (Fin n) → Fin (2 ^ Jbits n),
      μ.toOuterMeasure {lab | ∀ e ∈ S, lab e = f e} = ((2 : ENNReal) ^ Jbits n)⁻¹ ^ S.card

end DynConnWC


