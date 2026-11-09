-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_check_system
-- name    : QECDecodingHardness_AllThree_check_system
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:45.967977+00:00
-- url     : https://prove2.me/theorems/93fcafdf-091d-417e-8c94-e881369997a1
-- title:
--   Finite local faults, actual support weight, syndrome and minimum-error answers
-- statement:
--   Let Q and W be finite sets of error locations and constraints. A local fault has binary coordinates (x,z), and a finite check system specifies the contributions H_x and H_z of those coordinates. In a Z-only or measurement-fault system, x is required to vanish. For an assignment e, its syndrome and support weight are
--
--   $$\sigma_e(c)=\sum_{q\in Q}\bigl(H_x(c,q)x_q+H_z(c,q)z_q\bigr),\qquad |e|=|\{q:(x_q,z_q)\ne(0,0)\}|.$$
--
--   The sum is in the binary field. In particular, a Pauli Y, encoded as (1,1), has weight one. A minimum answer is any syndrome-consistent allowed error attaining the least weight. Infeasibility has a distinct answer and is never assigned minimum weight zero. Tanner incidence records whether some allowed local fault can trigger a check; adjacent supported locations share a Tanner neighbor.
--
--   This common finite interface handles both qubit Paulis and binary measurement faults. It also supplies the support and syndrome operations for the abstract counting lemmas; it does not assert that an arbitrary check matrix has any lattice geometry or hardness.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.3–5, Section II, finite decoding problems and Tanner graph

import Mathlib

namespace QECDecodingHardness.AllThree

abbrev Bit := ZMod 2
abbrev LocalFault := Bit × Bit

/-- Finite local binary fault system (Section II, pp.3–5).
`fromX`/`fromZ` are the contributions of the two local bits to each check.
For binary Z/data-or-measurement models, `allowX = false` and `fromX = 0`.
This interface is also used for the two abstract counting lemmas. It assumes
neither gadget truth tables nor any complexity claim. -/
structure CheckSystem where
  locations : ℕ
  checks : ℕ
  allowX : Bool
  fromX : Fin checks → Fin locations → Bit
  fromZ : Fin checks → Fin locations → Bit

abbrev Error (S : CheckSystem) := Fin S.locations → LocalFault
abbrev Syndrome (S : CheckSystem) := Fin S.checks → Bit

def Allowed (S : CheckSystem) (e : Error S) : Prop :=
  S.allowX = true ∨ ∀ q, (e q).1 = 0

def errorSupport {S : CheckSystem} (e : Error S) : Finset (Fin S.locations) :=
  Finset.univ.filter (fun q => e q ≠ 0)

def errorWeight {S : CheckSystem} (e : Error S) : ℕ := (errorSupport e).card

def syndrome (S : CheckSystem) (e : Error S) : Syndrome S :=
  fun c => ∑ q, (S.fromX c q * (e q).1 + S.fromZ c q * (e q).2)

def IsMinimumError (S : CheckSystem) (s : Syndrome S) (e : Error S) : Prop :=
  Allowed S e ∧ syndrome S e = s ∧
    ∀ f : Error S, Allowed S f → syndrome S f = s → errorWeight e ≤ errorWeight f

/-- No support reduction modulo stabilizers: this is the weight of an error,
not maximum likelihood of a degenerate equivalence class. A local (1,1) costs one. -/
def encodeError {S : CheckSystem} (e : Error S) : List Bool :=
  (List.finRange S.locations).flatMap (fun q => [decide ((e q).1 = 1), decide ((e q).2 = 1)])

/-- `false` alone denotes infeasibility; `true` prefixes an explicit minimizing error.
Every feasible input must have an attained minimizer, with every tie accepted. -/
def MinimumAnswer (S : CheckSystem) (s : Syndrome S) (answer : List Bool) : Prop :=
  (answer = [false] ∧ ¬ ∃ e : Error S, Allowed S e ∧ syndrome S e = s) ∨
  ∃ e : Error S, IsMinimumError S s e ∧ answer = true :: encodeError e

/-- Enumerated geometric coordinates determine, rather than constrain, the matrix. -/
def systemOfLists {Q C : Type} (qs : List Q) (cs : List C) (allowX : Bool)
    (hx hz : C → Q → Bit) : CheckSystem where
  locations := qs.length
  checks := cs.length
  allowX := allowX
  fromX := fun c q => hx (cs.get c) (qs.get q)
  fromZ := fun c q => hz (cs.get c) (qs.get q)

/-- Tanner adjacency is incidence of a possible elementary fault, respecting
which local bits are permitted. It is not Euclidean or Manhattan adjacency. -/
def Incident (S : CheckSystem) (q : Fin S.locations) (c : Fin S.checks) : Prop :=
  (S.allowX = true ∧ S.fromX c q ≠ 0) ∨ S.fromZ c q ≠ 0

def tannerGraph (S : CheckSystem) : SimpleGraph (Fin S.locations ⊕ Fin S.checks) where
  Adj u v := match u, v with
    | .inl q, .inr c => Incident S q c
    | .inr c, .inl q => Incident S q c
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

/-- Next nearest neighbors in the Tanner graph, on error locations. -/
def ErrorAdjacent (S : CheckSystem) (q r : Fin S.locations) : Prop :=
  q ≠ r ∧ ∃ c, Incident S q c ∧ Incident S r c

end QECDecodingHardness.AllThree


