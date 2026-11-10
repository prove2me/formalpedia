-- Prove2me | Definitions.Def_NogoodColoring1137_Main_DomainEncoding
-- name    : NogoodColoring1137_Main_DomainEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:51.170412+00:00
-- url     : https://prove2.me/theorems/220ce7e9-f459-428b-9fd0-a9a0626091d6
-- title:
--   Encoded heterogeneous domains and supplied nogood access
-- statement:
--   Encode $n$, all ordered domain sizes, $\ell$, and opaque binary data describing an implicit code. Scopes have $n$ membership bits. Words list their labels in scope order; boxes list every domain membership bit; a box list has a binary length header. NogoodAccess requires actual supplied-program runs returning sound certificates on every exact-$\ell$ scope.
--   $$T_{\rm construct}=\binom n\ell T_{\rm ng}+c(N+1)^e(n+1)^K\sigma nM\ell.$$
--   The input access contract supplies no code-membership or extension oracle. ConstructionTime charges oracle work and polynomial exact-bit overhead. The semantic code is not an executable program input.
--
--   This is the computational interface of Theorem 3. **Formalization Note** $N$ is header/data length plus $n$ scope bits. Constants describe uniform implementation overhead, not chosen per-instance costs.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §§2.1.2,4.2–4.3, pp.5,12–13

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Computation
import Definitions.Def_NogoodColoring1137_Main_Replay

namespace NogoodColoring1137.Main

def EncodeScope {n : ℕ} (T : Finset (Fin n)) : List Bool :=
  (List.finRange n).map (fun v => decide (v ∈ T))

def EncodeWord {n : ℕ} {d : Fin n → ℕ} {T : Finset (Fin n)} (s : Word d T) : List Bool :=
  ((T.sort (· ≤ ·)).attach).flatMap fun v =>
    EncodeNat (s ⟨v.val, by simpa using v.property⟩).val

def EncodeDomains {n : ℕ} (d : Fin n → ℕ) (ell : ℕ) (data : List Bool) : List Bool :=
  EncodeNat n ++ (List.finRange n).flatMap (fun v => EncodeNat (d v)) ++
    EncodeNat ell ++ EncodeNat data.length ++ data

def EncodeBox {n : ℕ} {d : Fin n → ℕ} (B : Box d) : List Bool :=
  (List.finRange n).flatMap fun v => (List.finRange (d v)).map (fun b => decide (b ∈ B v))

def EncodeBoxes {n : ℕ} {d : Fin n → ℕ} (B : List (Box d)) : List Bool :=
  EncodeNat B.length ++ B.flatMap EncodeBox

/-- Semantic access contract for the supplied nogood program on each exact ell-scope.
`data` is opaque input data describing the implicit code, never an extension oracle. -/
def NogoodAccess {n : ℕ} {d : Fin n → ℕ} (ell : ℕ)
    (Q : Code d Finset.univ) (data : List Bool)
    (oracle : IntMul.MultitapeTM) (Tng : ℝ) : Prop :=
  ∀ T : Finset (Fin n), T.card = ell → ∃ s : Word d T,
    Nogood Q T s ∧ Runs oracle
      (EncodeDomains d ell data ++ EncodeScope T) (EncodeWord s) Tng

/-- Polynomial overhead for exact bit arithmetic multiplies only the replay work. -/
noncomputable def ConstructionTime (n ell sigma K N : ℕ) (Tng c : ℝ) (e : ℕ) : ℝ :=
  (n.choose ell : ℝ) * Tng +
    c * ((N : ℝ)+1)^e * ((n+1 : ℕ)^K : ℝ) * sigma * n * ScopeCount n ell * ell

end NogoodColoring1137.Main


