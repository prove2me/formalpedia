-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Prefix
-- name    : AutoregressiveCompression_Main_Prefix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:39.88302+00:00
-- url     : https://prove2.me/theorems/8db8e004-a41e-41ac-a3e1-092c85507e43
-- title:
--   Size-indexed distribution classes and padded uniformly random prefixes
-- statement:
--   A source is a length N together with an arbitrary probability law on Σᴺ. A size-indexed distribution class is a collection of sets Dₙ of such sources, with N ≤ n for each member. No finiteness of Dₙ, samplability, rationality, decidable membership, monotonicity, or prefix closure is required.
--
--   A fixed prefix of length i retains the first min(i,N) symbols. Prefix closure means that every such truncation stays in the same size slice Dₙ. For a positive-length source, its random-prefix law independently draws X from the source and I uniformly from {1,…,N}, and returns
--
--   $$X_{\le I}\mathbin{\circ}\bot^{N-I}\in(\Sigma\cup\{\bot\})^N.$$
--
--   The padding symbol is fresh. The number of nonpadding symbols recovers I. For N = 0 the prefix law is the point mass on the empty word in the extended alphabet. The prefix class is exactly the image of each Dₙ under this construction, with its size index unchanged.
--
--   **Formalization Note** Words use zero-based Fin indices, original symbols are represented by `some`, and the padding symbol by `none`. A zero-based index j for the truncation position means I = j+1. The file includes the structural identity that a word padded at j contains exactly j+1 nonpadding symbols. This is a mathematical distribution interface, not a sample-generation algorithm.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Section 4.2, Definition 4.3 and footnote 5, printed p.16 / PDF p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Information

/-!
Hirahara–Nanashima, STOC 2027 submission #793 (October 2026), §4.2,
Definition 4.3 and footnote 5, printed p.16 / PDF p.18.
The fresh padding symbol is `none`, with original symbols embedded by `some`.
These are mathematical laws, not algorithms with free access to their masses.
-/

open scoped Classical

noncomputable section

namespace AutoregressiveCompression.Main

/-- A fixed-length word. Index zero represents source position one. -/
abbrev Word (Tok : Type) (N : ℕ) := Fin N → Tok

/-- A string law includes its length. It has no samplability or rationality
condition. -/
structure Source (Tok : Type) where
  length : ℕ
  law : PMF (Word Tok length)

/-- An arbitrary size-indexed class. No monotonicity, computability, finite-class
or prefix-closure condition is imposed. -/
structure DistributionClass (Tok : Type) where
  members : ℕ → Set (Source Tok)
  length_le : ∀ n D, D ∈ members n → D.length ≤ n

/-- First min(i,N) symbols, including i=0 and i≥N. -/
def truncate {Tok : Type} {N : ℕ} (i : ℕ) (x : Word Tok N) :
    Word Tok (min i N) :=
  fun j => x ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right i N)⟩

/-- Fixed-prefix pushforward of a source. -/
def Source.truncated {Tok : Type} (D : Source Tok) (i : ℕ) : Source Tok :=
  ⟨min i D.length, D.law.map (truncate i)⟩

/-- Definition 4.3: all truncations remain in the same size slice. -/
def DistributionClass.PrefixClosed {Tok : Type} (𝒟 : DistributionClass Tok) : Prop :=
  ∀ n D, D ∈ 𝒟.members n → ∀ i, D.truncated i ∈ 𝒟.members n

/-- For j:Fin N, retain j+1 original symbols, then pad to length N. -/
def padAt {Tok : Type} {N : ℕ} (x : Word Tok N) (j : Fin N) :
    Word (Option Tok) N :=
  fun k => if k.val ≤ j.val then some (x k) else none

/-- Random-prefix law. At positive length, the independent position j:Fin N
is uniform and means source I=j+1. At length zero there is a point mass on the
unique empty word, not a uniform draw from an empty set. -/
def prefixLaw {Tok : Type} {N : ℕ} (P : PMF (Word Tok N)) :
    PMF (Word (Option Tok) N) :=
  if h : N = 0 then
    PMF.pure (fun i => False.elim (by have := i.isLt; omega))
  else
    letI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    P.bind fun x => (PMF.uniformOfFintype (Fin N)).map (padAt x)

/-- Padded-prefix source, retaining the original length. -/
def Source.paddedPrefix {Tok : Type} (D : Source Tok) : Source (Option Tok) :=
  ⟨D.length, prefixLaw D.law⟩

/-- Prefix class is exactly the image in each slice; the size index is unchanged. -/
def DistributionClass.prefix {Tok : Type} (𝒟 : DistributionClass Tok) :
    DistributionClass (Option Tok) where
  members n := Source.paddedPrefix '' 𝒟.members n
  length_le n E hE := by
    obtain ⟨D, hD, rfl⟩ := hE
    exact 𝒟.length_le n D hD

/-- Count of symbols different from the fresh padding symbol. -/
def nonPaddingLength {Tok : Type} {N : ℕ} (y : Word (Option Tok) N) : ℕ :=
  (Finset.univ.filter fun k => (y k).isSome).card

/-- Padding encodes the source's truncation position without ambiguity. -/
@[simp] theorem nonPaddingLength_padAt {Tok : Type} {N : ℕ}
    (x : Word Tok N) (j : Fin N) :
    nonPaddingLength (padAt x j) = j.val + 1 := by
  have h : ((Finset.univ : Finset (Fin N)).filter fun k => (padAt x j k).isSome) =
      Finset.Iic j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    by_cases hk : k.val ≤ j.val
    · simp only [padAt, if_pos hk, Option.isSome_some, true_iff]
      exact hk
    · simp only [padAt, if_neg hk, Option.isSome_none, Bool.coe_false, false_iff]
      exact hk
  rw [nonPaddingLength, h, Fin.card_Iic]

/-- Recover the unpadded string by removing the fresh padding symbol. This is
used only on the support of prefixLaw when interpreting a random prefix. -/
def unpad {Tok : Type} {N : ℕ} (y : Word (Option Tok) N) : List Tok :=
  (List.ofFn y).filterMap id

end AutoregressiveCompression.Main


