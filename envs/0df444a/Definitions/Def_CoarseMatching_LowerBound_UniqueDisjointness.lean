-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_UniqueDisjointness
-- name    : CoarseMatching_LowerBound_UniqueDisjointness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:13.543515+00:00
-- url     : https://prove2.me/theorems/72e59190-b455-4399-8bf2-11c691040801
-- title:
--   Uniform Unique Disjointness XOR laws
-- statement:
--   In a universe of size $4m$, one Unique Disjointness instance is a uniform pair of $m$-subsets conditioned on intersection size $s\in\{0,1\}$, where $s$ is fair. Uniform relabeling of a canonical pair gives exactly this conditional law. For $t$ disjoint indexed universes the pairs are independent, and the target is
--
--   $$b=s_1\oplus\cdots\oplus s_t.$$
--
--   Conditioned on $b$, the remaining $t-1$ bits are uniform and the first is their XOR with $b$; independent uniform permutations then generate the pairs. The conditional acceptance gap compares the two parity-conditioned laws. All theorem uses have $m\ge1$ and $t\ge2$, where both parity cases are nonempty. Protocol cost is evaluated on pairs with both local set sizes $m$ and intersection size zero or one in each coordinate.
--
--   The finite game law imposes no finite-coin restriction on protocols and does not replace the distribution by independent uniform local subsets.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §4.3, printed p.13 (PDF p.14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_ProtocolResources

namespace CoarseMatching.LowerBound
noncomputable section

/-- Canonical m-subsets of a 4m-universe for the two intersection cases.
The second set uses the common element 0 in the one-intersection case. -/
def udLeft (m : ℕ) : Fin m ↪ Fin (4*m) :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun z : Fin (4*m) => z.val) h⟩

def udRight (m : ℕ) (s : Bool) : Fin m ↪ Fin (4*m) :=
  ⟨fun i => ⟨if s = true ∧ i.val = 0 then 0 else m+i.val-(if s then 1 else 0), by
      split_ifs <;> omega⟩,
    by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij
       dsimp at this; split_ifs at this <;> omega⟩

def udPair (m : ℕ) (s : Bool) (σ : Equiv.Perm (Fin (4*m))) :
    Finset (Fin (4*m)) × Finset (Fin (4*m)) :=
  ((Finset.univ.map (udLeft m)).map σ.toEmbedding,
   (Finset.univ.map (udRight m s)).map σ.toEmbedding)

/-- A uniform relabeling of a fixed pair is the uniform pair with its intersection
size: the symmetric group acts transitively, all fibers have equal cardinality.
This produces a normalized law without an empty-family conditional measure. -/
def udConditional (m : ℕ) (s : Bool) : PMF (Finset (Fin (4*m)) × Finset (Fin (4*m))) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin (4*m)))).map (udPair m s)

abbrev UDInput (m t : ℕ) := Fin t → Finset (Fin (4*m))

def parity (t : ℕ) (s : Fin t → Bool) : Bool := (List.ofFn s).foldl xor false

/-- Uniform bits conditioned on parity b: the remaining bits are independent fair
bits, and coordinate 0 is their xor with b. t≥1 in every use. -/
def parityBits (t : ℕ) (b : Bool) : PMF (Fin t → Bool) :=
  (PMF.uniformOfFintype (Fin t → Bool)).map fun s i =>
    if i.val = 0 then xor b ((List.ofFn s).drop 1 |>.foldl xor false) else s i

/-- Independent uniform permutations in disjoint indexed universes. Conditional
on the bit vector, each pair is uniform with the prescribed intersection size. -/
def udXorLaw (m t : ℕ) (b : Bool) : PMF (UDInput m t × UDInput m t) :=
  (parityBits t b).bind fun s =>
    (PMF.uniformOfFintype (Fin t → Equiv.Perm (Fin (4*m)))).map fun σ =>
      ((fun i => (udPair m (s i) (σ i)).1), (fun i => (udPair m (s i) (σ i)).2))

/-- Protocols are bounded on every pair of locally valid m-subset inputs,
with intersection size zero or one in each coordinate. -/
def UDInputs (m t : ℕ) (X Y : UDInput m t) : Prop :=
  (∀ i, (X i).card = m) ∧ (∀ i, (Y i).card = m) ∧
    ∀ i, (X i ∩ Y i).card ≤ 1

def udGap (m t : ℕ) (π : Protocol (UDInput m t) (UDInput m t)) : ℝ :=
  gap π (udXorLaw m t false) (udXorLaw m t true)

end
end CoarseMatching.LowerBound


