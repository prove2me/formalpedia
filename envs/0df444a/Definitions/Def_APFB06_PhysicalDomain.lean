-- Prove2me | Definitions.Def_APFB06_PhysicalDomain
-- name    : APFB06_PhysicalDomain
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:45:43.70137+00:00
-- url     : https://prove2.me/theorems/ed1b1d2d-384d-485d-8b02-afe4e9e27d93
-- title:
--   Raw distinctions and quotient tasks form an exact correspondence
-- statement:
--   Raw distinctions and quotient tasks form an exact correspondence. onPhysical uses the existing APFB01 quotient; taskEquiv proves both inverse laws and heldDistinctions maps the carried finite family without changing labels or price data. Boundaries: The source domain is Delta, not all Boolean functions on the quotient. Identifying physical B06 D with this image remains a source instantiation.
--
--   **Supplied data and hypotheses**
--
--   - hresp: every member of Delta respects equality of the supplied continuation profile
-- source:
--   Definitions/Def_APFB06_PhysicalDomain.lean; Sib v44 / pullbacks v1, SHA-256 70f08cb94362bbfb01f0c1618c7200aeca406a5393c34c8bf8f5093d81b36d73. Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101; Paper 5 Supplement v7.33:3034-3075 (remaining K1-K6 physical obligations); Frozen pullbacks/MANIFEST.txt and Notes passes1-6, hypothesis ledger, joint-class and held-relation ruling records; Actual codebank delta_calculus.py:165-188,236-300; continuation_calculus.py:76-140; quantum_frontend_closure.py:494-565,864-921

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFB06_PhysicalDomain
title: A raw distinction read on physical objects, and B06's distinction set as the physical distinction domain so read
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1313-1322 (physical descent of a distinction: a raw binary predicate d
 descends when there is a map on the quotient with d equal to that map after the quotient map; equivalently
 equivalent raw possibilities agree on d). Def_APF_B02_DeclaredInput (Delta, the physical distinction domain,
 as raw Boolean functions; its first clause is that descent). Def_APF_B06_DeclaredInput (Task: Boolean
 functions on the B01 quotient).
standing: a construction on the declared forms, which are unchanged. That B06's distinction set IS the
 domain built here is how B06 is instantiated in the theorems that use this module; it is the instantiation
 the two-object worlds already use.
statement: onPhysical d is the function on physical objects that the raw distinction d factors through.
 physicalDomain is the set of these for d in Delta. taskOfDistinction and distinctionOfTask pass between a
 raw distinction of Delta and the B06 task it gives; taskEquiv says they are inverse. heldDistinctions is
 the carried family of an alignment, written as raw distinctions.
not_claimed: that every Boolean function on physical objects is a distinction; any tested subfamily; any
 law on Delta beyond the descent it is given.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Mathlib.Data.Finset.Image

set_option autoImplicit false
namespace APFB06

/-- The function on physical objects through which a descending raw distinction factors. -/
def onPhysical {X Q : Type*} (Cont : X → Q → Prop) (d : X → Bool)
    (hd : ∀ x y, Cont x = Cont y → d x = d y) : APFB01.PhysicalState Cont → Bool :=
  Quot.lift d hd

/-- The physical distinction domain, read on physical objects. -/
def physicalDomain {X Q : Type*} (Cont : X → Q → Prop) (Delta : (X → Bool) → Prop)
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y) :
    Set (APFB01.PhysicalState Cont → Bool) :=
  {f | ∃ d : {d : X → Bool // Delta d}, f = onPhysical Cont d.val (hresp d)}

/-- A raw distinction of the domain, as a B06 task. -/
def taskOfDistinction {X Q : Type*} (Cont : X → Q → Prop) (Delta : (X → Bool) → Prop)
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y)
    (d : {d : X → Bool // Delta d}) : Task Cont (physicalDomain Cont Delta hresp) :=
  ⟨onPhysical Cont d.val (hresp d), d, rfl⟩

/-- A B06 task of the domain, as the raw distinction it reads. -/
def distinctionOfTask {X Q : Type*} (Cont : X → Q → Prop) (Delta : (X → Bool) → Prop)
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y)
    (t : Task Cont (physicalDomain Cont Delta hresp)) : {d : X → Bool // Delta d} :=
  ⟨fun x => t.val (APFB01.physicalClass Cont x), by
    obtain ⟨d, hd⟩ := t.property
    have h : (fun x => t.val (APFB01.physicalClass Cont x)) = d.val := by
      funext x
      rw [hd]
      rfl
    rw [h]
    exact d.property⟩

/-- Tasks of the domain and raw distinctions of the domain are the same things. -/
def taskEquiv {X Q : Type*} (Cont : X → Q → Prop) (Delta : (X → Bool) → Prop)
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y) :
    Task Cont (physicalDomain Cont Delta hresp) ≃ {d : X → Bool // Delta d} where
  toFun := distinctionOfTask Cont Delta hresp
  invFun := taskOfDistinction Cont Delta hresp
  left_inv := by
    intro t
    apply Subtype.ext
    funext c
    obtain ⟨a, rfl⟩ := Quot.exists_rep c
    rfl
  right_inv := by
    intro d
    apply Subtype.ext
    rfl

/-- The carried family of an alignment over the domain, written as raw distinctions. -/
def heldDistinctions {X Q : Type*} (Cont : X → Q → Prop) (Delta : (X → Bool) → Prop)
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y)
    (a : OriginalAlignment Cont (physicalDomain Cont Delta hresp)) :
    Finset {d : X → Bool // Delta d} :=
  a.carried.map (taskEquiv Cont Delta hresp).toEmbedding

end APFB06


