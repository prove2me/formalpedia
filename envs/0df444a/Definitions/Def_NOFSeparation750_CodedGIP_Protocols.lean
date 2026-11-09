-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_Protocols
-- name    : NOFSeparation750_CodedGIP_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:41:13.815219+00:00
-- url     : https://prove2.me/theorems/998bcdae-188a-4f22-9651-437a5fe8b83b
-- title:
--   Operational number-on-forehead bit protocols
-- statement:
--   For a product $X_1\times\cdots\times X_k$, player $i$ sees exactly the blocks with indices different from $i$. A deterministic protocol is a finite binary tree: the transcript fixes the speaker at each node, and that speaker's visible blocks determine the next bit. A leaf carries the publicly known Boolean answer. The cost on an input is the number of branch bits actually sent; a nonconstant final announcement is a paid bit.
--
--   Public randomness is represented by a finite distribution of such trees with arbitrary nonnegative real weights summing to one. The distribution is independent of the input, and its support may have any finite size. The bounded-cost predicate quantifies over every input and every seed. On the finite input spaces here, this includes every public-coin law through its finite set of bounded-communication behaviors, including exact non-dyadic coordinate sampling.
--
--   A nondeterministic protocol has one common fixed-length bit certificate and a deterministic verifier for each certificate. Correctness means
--   $$F(x)=1\quad\Longleftrightarrow\quad\exists z\;P_z(x)=1.$$
--   The total cost is the certificate length plus a common worst-case bound on verification communication. These definitions permit arbitrary interaction and adaptive speakers; they impose no special upper-bound protocol structure.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), §2, p.6, NOF communication; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib

namespace NOFSeparation750.CodedGIP

/-- Finite bit strings; zero length is allowed. -/
abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Input {k : ℕ} (X : Fin k → Type) := (i : Fin k) → X i
abbrev View {k : ℕ} (X : Fin k → Type) (i : Fin k) := (j : {j // j ≠ i}) → X j.val

def visible {k : ℕ} {X : Fin k → Type} (i : Fin k) (x : Input X) : View X i :=
  fun j => x j.val

/-- A bit protocol tree. The transcript determines the node and speaker, and the
query uses precisely that speaker's view. Leaves have public constant labels.
The final announcement of a nonconstant answer is itself a branch bit. -/
inductive BitProtocol {k : ℕ} (X : Fin k → Type) where
  | leaf (answer : Bool)
  | send (speaker : Fin k) (query : View X speaker → Bool)
      (zero one : BitProtocol X)

def BitProtocol.run {k : ℕ} {X : Fin k → Type} : BitProtocol X → Input X → Bool × ℕ
  | .leaf b, _ => (b, 0)
  | .send i f p₀ p₁, x =>
    let out := if f (visible i x) then p₁.run x else p₀.run x
    (out.1, out.2 + 1)

def BitProtocol.Bounded {k : ℕ} {X : Fin k → Type} (P : BitProtocol X) (d : ℕ) : Prop :=
  ∀ x, (P.run x).2 ≤ d

/-- A real finite public-coin law, independent of the input. On a finite input
space with bounded communication this represents arbitrary public randomness:
there are only finitely many deterministic behaviors. Weights need not be dyadic. -/
structure PublicProtocol {k : ℕ} (X : Fin k → Type) where
  seeds : ℕ
  weight : Fin seeds → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1
  tree : Fin seeds → BitProtocol X

def PublicProtocol.Bounded {k : ℕ} {X : Fin k → Type} (P : PublicProtocol X) (d : ℕ) : Prop :=
  ∀ s, (P.tree s).Bounded d

noncomputable def PublicProtocol.acceptance {k : ℕ} {X : Fin k → Type}
    (P : PublicProtocol X) (x : Input X) : ℝ :=
  ∑ s, if ((P.tree s).run x).1 then P.weight s else 0

def PublicProtocol.OneSided {k : ℕ} {X : Fin k → Type}
    (P : PublicProtocol X) (F : Input X → Bool) (error : ℝ) : Prop :=
  (∀ x, F x = true → P.acceptance x = 1) ∧
  (∀ x, F x = false → P.acceptance x ≤ error)

/-- Common fixed-length certificate and an unrestricted interactive verifier. -/
structure NondetProtocol {k : ℕ} (X : Fin k → Type) where
  certificateBits : ℕ
  verifier : Bits certificateBits → BitProtocol X

def NondetProtocol.Correct {k : ℕ} {X : Fin k → Type}
    (P : NondetProtocol X) (F : Input X → Bool) : Prop :=
  ∀ x, F x = true ↔ ∃ z, ((P.verifier z).run x).1 = true

def NondetProtocol.Bounded {k : ℕ} {X : Fin k → Type}
    (P : NondetProtocol X) (d : ℕ) : Prop :=
  ∃ c, P.certificateBits + c ≤ d ∧ ∀ z, (P.verifier z).Bounded c

end NOFSeparation750.CodedGIP


