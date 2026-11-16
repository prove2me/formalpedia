-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_Merkle
-- name    : FourMsgQMA_Supplement_Merkle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:32.133395+00:00
-- url     : https://prove2.me/theorems/becf3940-f153-4c28-bd36-b79995d74d87
-- title:
--   Balanced Merkle commitments with local openings and their binding (Def 3.13)
-- statement:
--   A **hash family with local openings** $\mathrm{MT}=(\mathrm{Gen},\mathrm{Commit},\mathrm{Open},\mathrm{Verify})$ commits to a vector of $k$ blocks in $\{0,1\}^m$. It is instantiated here as a balanced Merkle tree over a keyed hash family $H$: the tree has depth $D=\lceil\log_2k\rceil$ and $2^D$ leaves (missing blocks read as zero), each level has its own key, a leaf hashes $0\,\|\,\mathrm{bin}(j)\,\|\,x_j$ and an internal node $1\,\|\,\mathrm{bin}(j)\,\|\,\text{left}\,\|\,\text{right}$ (domain separation by node position and block index). $\mathrm{Open}(hk,x,i)$ is the authentication path of sibling digests, and $\mathrm{Verify}(hk,\alpha,i,x_i,\rho)$ recomputes the root, rejecting out-of-range positions and malformed lengths.
--
--   **Binding of local openings** (Definition 3.13): for every polynomial $k,m$ and every QPT adversary receiving $hk$ and outputting $(\alpha,i,x_0,x_1,\rho_0,\rho_1)$,
--   $$
--   \Pr\big[x_0\ne x_1\ \wedge\ \mathrm{Verify}(hk,\alpha,i,x_0,\rho_0)=1\ \wedge\ \mathrm{Verify}(hk,\alpha,i,x_1,\rho_1)=1\big]\le\nu(\lambda)
--   $$
--   for a negligible $\nu$.
--
--   The module also defines the Merkle commitment to a bit vector, $x\mapsto\mathrm{Commit}(hk,x)$ with one-bit blocks, as a keyed hash family, so that "collapsing of the vector commitment" (p.16) is Definition 3.12 for that family with the whole vector as preimage register.
--
--   **Formalization Note** Pinned-down tree layout (operator request); positions are $0,\dots,k-1$, the paper's $i\in[k]$ being position $i-1$.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.8 and Definition 3.13, p.16 (PDF 18)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.8 (p.16, PDF 18): hash families with
succinct local openings `MT = (Gen, Commit, Open, Verify)`, instantiated as balanced Merkle trees
built from a keyed hash family ("We use balanced Merkle trees built from … collapsing hashes …
Domain separation includes node positions and block indices"), and binding of local openings
(Definition 3.13).

Pinned-down version (operator request) of the tree: for `k` blocks of `m` bits, the tree has depth
`D = ⌈log₂ k⌉` and `2^D` leaves (missing blocks read as zeros); positions are `0, …, k − 1` (the
paper's `i ∈ [k]` is position `i − 1`); level `h` (`h = 0` the leaves) uses its own key
`hk_h ← Gen(1^λ, ℓ_h)` for its input length `ℓ_h`. A leaf hashes `0 ‖ bin(j) ‖ x_j`, an internal
node `1 ‖ bin(j) ‖ left ‖ right`, with `bin(j)` the `D + 1`-bit index of the node in its level.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- The depth `D = ⌈log₂ k⌉` of the tree for `k` blocks. -/
def merkleDepth (k : ℕ) : ℕ := clog2 k

/-- The input length `ℓ_h` of the hash at level `h`: `1 + (D + 1) + m` at the leaves and
`1 + (D + 1) + 2 d_H(λ, ℓ_{h-1})` above. -/
def merkleIn (H : HashFamily) (lam k m : ℕ) : ℕ → ℕ
  | 0 => 1 + (merkleDepth k + 1) + m
  | h + 1 => 1 + (merkleDepth k + 1) + 2 * H.digestLen lam (merkleIn H lam k m h)

/-- The offset of the coins of level `h` in the key-generation tape. -/
def merkleCoinOff (H : HashFamily) (lam k m h : ℕ) : ℕ :=
  ∑ h' ∈ Finset.range h, H.genCoins lam (merkleIn H lam k m h')

/-- The number of coins of `MT.Gen(1^λ, k, m)`: one key per level `0, …, D`. -/
def merkleCoins (H : HashFamily) (lam k m : ℕ) : ℕ := merkleCoinOff H lam k m (merkleDepth k + 1)

/-- `hk ← MT.Gen(1^λ, k, m)`: the packed list of the `D + 1` level keys, from independent coins. -/
def merkleGen (H : HashFamily) (lam k m : ℕ) (r : Bits) : Bits :=
  pack ((List.range (merkleDepth k + 1)).map fun h =>
    H.gen lam (merkleIn H lam k m h)
      ((r.drop (merkleCoinOff H lam k m h)).take (H.genCoins lam (merkleIn H lam k m h))))

/-- The digest of node `j` at level `h` of the tree of the block vector `x` (blocks padded or cut to
`m` bits, missing blocks zero) under the level keys `keys`. -/
def merkleNode (H : HashFamily) (k m : ℕ) (keys : List Bits) (x : List Bits) : ℕ → ℕ → Bits
  | 0, j => H.hash (keys.getD 0 []) ([false] ++ idxBits (merkleDepth k + 1) j ++ padTo m (x.getD j []))
  | h + 1, j => H.hash (keys.getD (h + 1) [])
      ([true] ++ idxBits (merkleDepth k + 1) j ++ merkleNode H k m keys x h (2 * j) ++
        merkleNode H k m keys x h (2 * j + 1))

/-- `MerkleRoot_hk(x) = Commit(hk, x)`: the root digest. -/
def merkleCommit (H : HashFamily) (k m : ℕ) (hk : Bits) (x : List Bits) : Bits :=
  merkleNode H k m (unpack hk) x (merkleDepth k) 0

/-- The index of the sibling of the level-`h` ancestor of leaf `j`. -/
def merkleSib (j h : ℕ) : ℕ := if (j / 2 ^ h) % 2 = 0 then j / 2 ^ h + 1 else j / 2 ^ h - 1

/-- `Open(hk, x, j)`: the packed authentication path, the sibling digests from the leaf level up. -/
def merkleOpen (H : HashFamily) (k m : ℕ) (hk : Bits) (x : List Bits) (j : ℕ) : Bits :=
  pack ((List.range (merkleDepth k)).map fun h => merkleNode H k m (unpack hk) x h (merkleSib j h))

/-- The digest recomputed at level `h` from the claimed block `b` at position `j` and the path. -/
def merkleClimb (H : HashFamily) (k m : ℕ) (keys path : List Bits) (j : ℕ) (b : Bits) : ℕ → Bits
  | 0 => H.hash (keys.getD 0 []) ([false] ++ idxBits (merkleDepth k + 1) j ++ b)
  | h + 1 =>
      let cur := merkleClimb H k m keys path j b h
      let sib := path.getD h []
      H.hash (keys.getD (h + 1) [])
        ([true] ++ idxBits (merkleDepth k + 1) (j / 2 ^ (h + 1)) ++
          (if (j / 2 ^ h) % 2 = 0 then cur ++ sib else sib ++ cur))

/-- `Verify(hk, α, j, b, ρ)`: rejects an out-of-range position (`j ≥ k`), a block of the wrong length,
a path of the wrong length or with a sibling digest of the wrong length, and otherwise accepts
exactly when the recomputed root equals `α`. -/
def merkleVerify (H : HashFamily) (lam k m : ℕ) (hk α : Bits) (j : ℕ) (b ρ : Bits) : Bool :=
  let path := unpack ρ
  decide (j < k) && decide (b.length = m) && decide (path.length = merkleDepth k) &&
    ((List.range (merkleDepth k)).all fun h =>
      decide ((path.getD h []).length = H.digestLen lam (merkleIn H lam k m h))) &&
    decide (merkleClimb H k m (unpack hk) path j b (merkleDepth k) = α)

/-- The binding experiment of Definition 3.13 (p.16) for `(k, m)(λ)`, as a published
`TightPQRepetition.Main.Verifier` (semantic carrier): the adversary receives `hk ← MT.Gen(1^λ, k, m)`
and answers `pack [α, j, x₀, x₁, ρ₀, ρ₁]` (`j` in binary); it wins when `x₀ ≠ x₁` and both openings
verify at position `j` under `α`. -/
def merkleBindVerifier (H : HashFamily) (k m : ℕ → ℕ) : Verifier where
  rounds := fun _ => 1
  coins := fun lam => merkleCoins H lam (k lam) (m lam)
  qLen := fun _ _ => 0
  query := fun lam r _ _ => merkleGen H lam (k lam) (m lam) r
  verdict := fun lam r τ =>
    let hk := merkleGen H lam (k lam) (m lam) r
    let a := unpack (τ.getD 0 ([], [])).2
    let j := bitsVal (a.getD 1 [])
    decide (a.getD 2 [] ≠ a.getD 3 []) &&
      merkleVerify H lam (k lam) (m lam) hk (a.getD 0 []) j (a.getD 2 []) (a.getD 4 []) &&
      merkleVerify H lam (k lam) (m lam) hk (a.getD 0 []) j (a.getD 3 []) (a.getD 5 [])

/-- Binding of local openings, Definition 3.13 (p.16): for all polynomial `k, m` and every QPT
adversary, the winning probability is negligible. -/
def MerkleBinding (H : HashFamily) : Prop :=
  ∀ k m : ℕ → ℕ, PolyBound k → PolyBound m → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, (Adv lam).acceptProb (merkleBindVerifier H k m) lam ≤ ν lam

/-- The Merkle commitment to a bit vector, `x ↦ Commit(hk, x)` with one-bit blocks, as a keyed hash
family: `Gen(1^λ, ℓ) = MT.Gen(1^λ, ℓ, 1)` and `Hash(hk, x) = MerkleRoot_hk(x)` (`k = |x|`), with the
root digest length. "Collapsing of the vector commitment means Definition 3.12 for the map
`x ↦ Commit(hk, x)`, with the whole vector as the preimage register" (p.16). -/
def merkleBitHash (H : HashFamily) : HashFamily where
  genCoins := fun lam l => merkleCoins H lam l 1
  gen := fun lam l r => merkleGen H lam l 1 r
  digestLen := fun lam l => H.digestLen lam (merkleIn H lam l 1 (merkleDepth l))
  hash := fun hk x => merkleCommit H x.length 1 hk (x.map fun b => [b])

end Supplement

end FourMsgQMA


