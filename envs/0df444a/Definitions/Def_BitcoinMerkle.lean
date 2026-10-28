-- Prove2me | Definitions.Def_BitcoinMerkle
-- name    : BitcoinMerkle
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T04:25:10.904011+00:00
-- url     : https://prove2.me/theorems/af89e80d-23e7-4c0a-9f09-18a6ec9a3655
-- title:
--   ComputeMerkleRoot with Bitcoin's odd-level duplication and mutation check
-- statement:
--   Hashes form an arbitrary type $H$ with decidable equality. The pairwise hash (`SHA256D64` on two concatenated hashes in the source) is an abstract function $c : H \to H \to H$, and the all-zero hash returned for an empty list is an abstract $z : H$.
--
--   **One level.** $\mathrm{pairUp}_c$ maps a list to the list of $c(\ell_{2i}, \ell_{2i+1})$ over aligned pairs; an odd trailing element $a$ contributes $c(a, a)$, which is the source's `hashes.push_back(hashes.back())` followed by pairwise hashing. Its length is $\lceil |\ell| / 2 \rceil$ (`pairUp_length`, used to justify termination).
--
--   **The mutation test.** $\mathrm{hasEqualPair}(\ell)$ is true when some aligned pair $(\ell_{2i}, \ell_{2i+1})$ with $2i+1 < |\ell|$ has equal entries. The duplicated trailing element is not tested, because in the source the test runs before the duplication.
--
--   **The loop.** $\mathrm{rootLoop}_{c,z}(\ell, m)$: while $|\ell| > 1$, replace $m$ by $m \lor \mathrm{hasEqualPair}(\ell)$ and $\ell$ by $\mathrm{pairUp}_c(\ell)$; on exit return the remaining hash (or $z$ for an empty list) together with $m$.
--
--   **The root.** $\mathrm{computeMerkleRoot}_{c,z}(\ell) = \mathrm{rootLoop}_{c,z}(\ell, \mathtt{false})$, a pair (root, mutated), as `ComputeMerkleRoot(hashes, &mutated)`.
--
--   These definitions fix the semantics of the block Merkle root and of the CVE-2012-2459 defence for use by block-structure validation.
--
--   **Formalization Note.** `rootLoop` is defined by well-founded recursion on the list length. Equality in `hasEqualPair` is `decide (a = b)` on $H$. Nothing is assumed about $c$; in particular no collision-resistance. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Std

namespace BitcoinMerkle

/-! Transcription of `ComputeMerkleRoot` (`src/consensus/merkle.cpp`, Bitcoin Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`). Hashes are an arbitrary type `H` with decidable
equality; the pairwise hash `SHA256D64` on two concatenated hashes is an abstract function
`c : H → H → H`, and `uint256()` (the all-zero hash returned for an empty list) is an abstract
`z : H`. The loop body is: flag any equal aligned pair `(pos, pos + 1)` of the current level
(`pos` even, `pos + 1 < size`), duplicate the last element when the level has odd length, hash
adjacent pairs, and continue while more than one hash remains. -/

variable {H : Type} [DecidableEq H]

/-- One level of the tree: hash adjacent pairs; an odd trailing element is hashed with itself,
which is `hashes.push_back(hashes.back())` followed by `SHA256D64`. -/
def pairUp (c : H → H → H) : List H → List H
  | a :: b :: rest => c a b :: pairUp c rest
  | [a] => [c a a]
  | [] => []

/-- The mutation test of one level: some aligned pair `(pos, pos + 1)` with `pos` even and
`pos + 1 < size` consists of equal hashes. The duplicated trailing element is not tested. -/
def hasEqualPair : List H → Bool
  | a :: b :: rest => decide (a = b) || hasEqualPair rest
  | _ => false

omit [DecidableEq H] in
theorem pairUp_length (c : H → H → H) : ∀ l : List H, (pairUp c l).length = (l.length + 1) / 2
  | a :: b :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length c rest]
    omega
  | [a] => by simp [pairUp]
  | [] => by simp [pairUp]

/-- The `while (hashes.size() > 1)` loop with its running `mutation` flag. -/
def rootLoop (c : H → H → H) (z : H) (hs : List H) (mutation : Bool) : H × Bool :=
  if _h : 1 < hs.length then
    rootLoop c z (pairUp c hs) (mutation || hasEqualPair hs)
  else
    (hs.headD z, mutation)
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega

/-- `ComputeMerkleRoot(hashes, mutated)`: the root and the mutation flag. -/
def computeMerkleRoot (c : H → H → H) (z : H) (hs : List H) : H × Bool :=
  rootLoop c z hs false

end BitcoinMerkle


