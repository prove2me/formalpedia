-- Prove2me | Definitions.Def_FixpReciprocal_squareProblem
-- name    : FixpReciprocal_squareProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:06.250824+00:00
-- url     : https://prove2.me/theorems/1f43f581-a4c5-4cbf-ba3f-bbe0cf47665e
-- title:
--   The generalized-circuit problem of Lemma 3.4
-- statement:
--   This is the generalized-circuit problem over the three gate functions
--   $$u\mapsto1-u,\qquad(u,v)\mapsto[\![u+v]\!],\qquad u\mapsto u^2.$$
--   An instance is a list of $N\ge1$ gates with input indices in $[N]$, cycles allowed. A solution is a vector $x\in[0,1]^N$ satisfying every gate equation.
--
--   It is the FIXP-complete problem from which the paper reduces.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Lemma 3.4, p.11 (PDF p.13); Definition 3.3, pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_clip
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace FixpReciprocal

open OnlineCRS.Combine

/-- **The gates of Lemma 3.4:** `u ↦ 1 − u`, `(u, v) ↦ ⟦u + v⟧`, `u ↦ u²`, with input indices.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Lemma 3.4, p.11. -/
inductive SqGate where
  | compl (j : ℕ)
  | clipSum (j k : ℕ)
  | sq (j : ℕ)

/-- The right-hand side of the gate equation. -/
noncomputable def SqGate.eval (v : ℕ → ℝ) : SqGate → ℝ
  | .compl j => 1 - v j
  | .clipSum j k => clip (v j + v k)
  | .sq j => v j ^ 2

/-- The gate's input indices are below `N`. -/
def SqGate.ReadsBelow (N : ℕ) : SqGate → Prop
  | .compl j => j < N
  | .clipSum j k => j < N ∧ k < N
  | .sq j => j < N

/-- A circuit of gates of Lemma 3.4 (Definition 3.3): `N ≥ 1` gates, indices in `[N]`. -/
def SqValid (C : List SqGate) : Prop :=
  1 ≤ C.length ∧ ∀ g ∈ C, g.ReadsBelow C.length

/-- The solutions of such a circuit (Definition 3.3). -/
def SqCircuitSol (C : List SqGate) : Set (Fin C.length → ℝ) :=
  {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i : Fin C.length, x i = (C.get i).eval (lookup x)}

/-- Numeric form of a gate. -/
def SqGate.code : SqGate → ℕ × ℕ × ℕ
  | .compl j => (0, j, 0)
  | .clipSum j k => (1, j, k)
  | .sq j => (2, j, 0)

theorem SqGate.code_injective : Function.Injective SqGate.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [SqGate.code]

/-- Binary encoding of a gate. -/
def encSqGate (g : SqGate) : List Sym := fNat g.code.1 ++ fNat g.code.2.1 ++ fNat g.code.2.2

theorem encSqGate_prefixFree : PrefixFree encSqGate := by
  intro a b s t h
  simp only [encSqGate, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := fNat_prefixFree h
  obtain ⟨h3, h⟩ := fNat_prefixFree h
  exact ⟨SqGate.code_injective (Prod.ext h1 (Prod.ext h2 h3)), h⟩

/-- **Finding a solution to an `F`-generalized circuit, for `F` the three gate functions of Lemma 3.4.**

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Lemma 3.4, p.11; Definition 3.3, pp.10–11. -/
def squareProblem : RealSearch where
  Inst := {C : List SqGate // SqValid C}
  enc := fun I => fList encSqGate I.1
  enc_injective := fun _ _ h => Subtype.ext (encSqGate_prefixFree.fList.injective h)
  dim := fun I => I.1.length
  Sol := fun I => SqCircuitSol I.1

end FixpReciprocal


