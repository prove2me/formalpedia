-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_PSM
-- name    : SymmetricPSM1041_ORLowerBound_PSM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:12.653821+00:00
-- url     : https://prove2.me/theorems/323e801d-19df-417b-aa85-a510e7dc7ac7
-- title:
--   §2.1 — private simultaneous messages, correctness and privacy
-- statement:
--   A private simultaneous messages protocol has a finite nonempty shared seed set $R$, declared local alphabets $\mathcal M_i\subseteq\{0,1\}^*$, local maps $M_i:\{0,1\}\times R\to\mathcal M_i$, and a decoder $\operatorname{Rec}:\prod_i\mathcal M_i\to\{0,1\}$. The seed is uniform, shared by the parties, and hidden from the decoder. Each party sees only its own bit. Write
--
--   $$M(x,r)=(M_i(x_i,r))_i,\qquad \operatorname{Supp}_P(x)=\{M(x,r):r\in R\}.$$
--
--   Perfect correctness for $f$ means $\operatorname{Rec}(M(x,r))=f(x)$ for every input and seed. Support privacy means equal supports whenever $f(x)=f(y)$. Perfect privacy means equal transcript laws for such pairs; with one uniform finite seed space this is exactly equality of every transcript's seed-fiber counts. OR is true exactly when some bit is true, and AND exactly when every bit is true.
--
--   These objects provide the operational interface for the lower bounds. Correctness and privacy are predicates, not requirements built into the protocol structure. Messages are arbitrary finite binary lists, including the empty list; the declared alphabets may contain unused symbols.
--
--   **Formalization Note** An arbitrary finite nonempty $R$ is reindexed by $\operatorname{Fin}(|R|)$; the seed count is unrestricted. The definitions accept a general party index type so restrictions use their actual free coordinates. No symmetry of the protocol, fixed message length, prefix-code condition, or privacy strengthening is imposed.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), pp. 6–7, §2.1, Eq. (1); p. 6, Boolean functions; p. 3, Theorem 1 (AND)

import Mathlib

namespace SymmetricPSM1041.ORLowerBound

/-- Finite, possibly empty binary strings; their list lengths are the actual costs. -/
abbrev Message := List Bool

/-- A general private simultaneous messages protocol. No privacy or correctness is built in.
The same uniformly sampled seed is used by every party. Declared alphabets may have unused
symbols; the local maps depend only on a party's own input bit and the shared seed. -/
structure PSM (ι : Type*) where
  seedCount : ℕ
  seedCount_pos : 0 < seedCount
  alphabet : ι → Set Message
  message : (i : ι) → Bool → Fin seedCount → {w : Message // w ∈ alphabet i}
  decode : ((i : ι) → {w : Message // w ∈ alphabet i}) → Bool

abbrev Transcript {ι : Type*} (P : PSM ι) :=
  (i : ι) → {w : Message // w ∈ P.alphabet i}

def transcript {ι : Type*} (P : PSM ι) (x : ι → Bool) (r : Fin P.seedCount) :
    Transcript P := fun i => P.message i (x i) r

def transcriptSupport {ι : Type*} (P : PSM ι) (x : ι → Bool) : Set (Transcript P) :=
  Set.range (transcript P x)

def PerfectCorrect {ι : Type*} (P : PSM ι) (f : (ι → Bool) → Bool) : Prop :=
  ∀ x r, P.decode (transcript P x r) = f x

def SupportPrivate {ι : Type*} (P : PSM ι) (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f x = f y → transcriptSupport P x = transcriptSupport P y

/-- Equal fiber counts give equality of laws under the same finite uniform seed. -/
noncomputable def PerfectPrivate {ι : Type*} (P : PSM ι)
    (f : (ι → Bool) → Bool) : Prop := by
  classical
  exact ∀ x y, f x = f y → ∀ v : Transcript P,
    (Finset.univ.filter (fun r => transcript P x r = v)).card =
    (Finset.univ.filter (fun r => transcript P y r = v)).card

noncomputable def orFunction {ι : Type*} (x : ι → Bool) : Bool := by
  classical
  exact decide (∃ i, x i = true)

noncomputable def andFunction {ι : Type*} (x : ι → Bool) : Bool := by
  classical
  exact decide (∀ i, x i = true)

end SymmetricPSM1041.ORLowerBound


