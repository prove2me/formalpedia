-- Prove2me | Definitions.Def_RoundedPotentials_Main_Supplement_Streaming
-- name    : RoundedPotentials_Main_Supplement_Streaming
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:03:36.482833+00:00
-- url     : https://prove2.me/theorems/de79d0e9-181b-4587-98fc-1b0493e3f895
-- title:
--   Turnstile streams, online annotation schemes and certificate-first verifiers (§4.1)
-- statement:
--   This file defines the two streaming models of §4.1. In both, memory is measured in bits. The working memory is a bit string and the transitions are arbitrary functions, which is the usual non-uniform streaming model.
--
--   1. A **turnstile update** $(u,v,\Delta)$ with $\Delta\in\mathbb Z$ adds $\Delta$ to the capacity of the ordered pair $(u,v)$. The final capacity is the sum of the updates on that pair. The promise of Theorem 4.1 says that updates are on distinct vertices and that every final capacity lies in $\{0,\dots,W\}$; intermediate values are unrestricted.
--   2. An **online annotation scheme** draws `coinBits` private uniform bits and forms its initial memory from them, so retained coins count as space. It updates its memory on each stream item and then on each help bit, all of which arrive after the stream. Finally it outputs a value or rejects. `memories` lists every memory content of a run, and the space of a run is the largest length in that list. `prob` is the probability over uniform coins.
--   3. A **certificate-first** item $(u,v,c)$ contributes $c\ge0$ to the pair $(u,v)$; several items may concern the same pair. The promise of Corollary 4.3 says that the items are loopless and that the total capacity per ordered pair is at most $W$. A deterministic verifier holds the certificate in read-only random-access memory before the stream: every transition may read all of it, and it is not charged as working space. Its working memory is a bit string. `accepts` gives its decision after one pass.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 19, §4.1 (model paragraph), Theorem 4.1, Corollary 4.3

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Graphs

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

/-! # Streams, online annotation schemes and certificate-first verifiers (§4.1)

Space is measured in bits: a verifier's whole working memory is a bit string, and its
transitions are arbitrary functions (the usual non-uniform streaming model, which charges memory,
help and certificate bits but not computation). Private randomness is a uniformly random bit
string that the verifier sees only through its initial memory, so retained coins are charged as
space. -/

/-- A turnstile update `(u, v, Δ)`: add `Δ ∈ ℤ` to the capacity of the ordered pair `(u, v)`. -/
abbrev Update (n : ℕ) := Fin n × Fin n × ℤ

/-- The final capacity of `(u, v)` after the turnstile stream `σ`: the sum of its updates. -/
def finalCap {n : ℕ} (σ : List (Update n)) (u v : Fin n) : ℤ :=
  (σ.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum

/-- The promise of Theorem 4.1: every update is on an ordered pair of distinct vertices
(§2 graphs are loopless) and every final capacity lies in `{0, …, W}`. Intermediate
capacities are unrestricted. -/
def TurnstilePromise {n : ℕ} (W : ℕ) (σ : List (Update n)) : Prop :=
  (∀ e ∈ σ, e.1 ≠ e.2.1) ∧ ∀ u v, 0 ≤ finalCap σ u v ∧ finalCap σ u v ≤ (W : ℤ)

/-- The final capacity matrix of a turnstile stream (as natural numbers; under the promise this
is `finalCap`). -/
def streamCap {n : ℕ} (σ : List (Update n)) (u v : Fin n) : ℕ := (finalCap σ u v).toNat

/-- An online annotation scheme on `[n]` in which all help follows the input stream. The
verifier draws `coinBits` private uniform bits, forms its initial memory from them, updates its
memory on every stream item, then on every help bit, and finally outputs a value or rejects
(`none`). -/
structure AnnotationScheme (n : ℕ) where
  coinBits : ℕ
  init : (Fin coinBits → Bool) → List Bool
  update : List Bool → Update n → List Bool
  readHelp : List Bool → Bool → List Bool
  output : List Bool → Option ℕ

namespace AnnotationScheme

variable {n : ℕ} (S : AnnotationScheme n)

/-- Memory after the stream. -/
def afterStream (r : Fin S.coinBits → Bool) (σ : List (Update n)) : List Bool :=
  σ.foldl S.update (S.init r)

/-- Every memory content of the run on coins `r`, stream `σ` and help `h`, in order. -/
def memories (r : Fin S.coinBits → Bool) (σ : List (Update n)) (h : List Bool) :
    List (List Bool) :=
  σ.scanl S.update (S.init r) ++ (h.scanl S.readHelp (S.afterStream r σ)).tail

/-- The output (a value, or `none` = reject) of the run on coins `r`, stream `σ`, help `h`. -/
def result (r : Fin S.coinBits → Bool) (σ : List (Update n)) (h : List Bool) : Option ℕ :=
  S.output (h.foldl S.readHelp (S.afterStream r σ))

open Classical in
/-- The probability, over uniform coins, of an event about the coins. -/
noncomputable def prob (E : (Fin S.coinBits → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter (fun r => E r)).card : ℝ) / 2 ^ S.coinBits

end AnnotationScheme

/-- A certificate-first stream item: a directed edge `(u, v)` with a nonnegative capacity
contribution. Several items may concern the same ordered pair. -/
abbrev Contribution (n : ℕ) := Fin n × Fin n × ℕ

/-- The total capacity of `(u, v)` in a contribution stream. -/
def aggCap {n : ℕ} (σ : List (Contribution n)) (u v : Fin n) : ℕ :=
  (σ.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum

/-- The promise of Corollary 4.3: loopless items and total capacity at most `W` per ordered
pair. -/
def ContributionPromise {n : ℕ} (W : ℕ) (σ : List (Contribution n)) : Prop :=
  (∀ e ∈ σ, e.1 ≠ e.2.1) ∧ ∀ u v, aggCap σ u v ≤ W

/-- A deterministic one-pass certificate-first verifier: the certificate `z` is in read-only
random-access memory before the stream (every transition may read all of it, and it is not
charged as working space); the working memory is a bit string. -/
structure CertFirstVerifier (n : ℕ) where
  init : List Bool → List Bool
  update : List Bool → List Bool → Contribution n → List Bool
  accept : List Bool → List Bool → Bool

namespace CertFirstVerifier

variable {n : ℕ} (V : CertFirstVerifier n)

/-- Every working-memory content of the run with certificate `z` on stream `σ`. -/
def memories (z : List Bool) (σ : List (Contribution n)) : List (List Bool) :=
  σ.scanl (V.update z) (V.init z)

/-- The decision of the run with certificate `z` on stream `σ`. -/
def accepts (z : List Bool) (σ : List (Contribution n)) : Bool :=
  V.accept z (σ.foldl (V.update z) (V.init z))

end CertFirstVerifier

end RoundedPotentials.Main.Supplement


