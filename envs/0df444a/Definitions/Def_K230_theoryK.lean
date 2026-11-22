-- Prove2me | Definitions.Def_K230_theoryK
-- name    : K230_theoryK
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:15.177622+00:00
-- url     : https://prove2.me/theorems/f684a976-737a-4885-ac94-b0c8f3af5e87
-- title:
--   K230: the compact theory K
-- statement:
--   The compact first-order set theory K. For a matrix $\varphi$, `emittedClosure φ` asserts that whenever an input lies in a container, the container supplies an output of $\varphi$ and is closed under subset-witness requests; `kprimeCore φ` is its output-root universal closure. `KPrimeOrd` is the theory of equality axioms plus all closed universal instances of `kprimeCore`; `KPrimeOrdIR` adds irreflexivity $\forall x\,\neg(x\in x)$. Ports `KPrimeCore.v`, `KPrimeTheory.v`, `KP0.v`, `KPSeed.v`, `KPRaw.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KPrimeTheory.v

import Definitions.Def_K230_fol
namespace K230
def rawSubset (a b : Nat) : Form := .all (.impl (mem 0 (a + 1)) (mem 0 (b + 1)))
def emittedClosure (φ : Form) : Form :=
  .all (.impl (mem 0 1)
    (.ex (.conj (subst φ (scons 1 (scons 0 (fun k => 4 + k))))
      (.all (.impl (rawSubset 0 2)
        (.all (.impl (subst φ (scons 0 (scons 1 (fun k => 6 + k))))
          (.ex (.conj (subst φ (scons 0 (scons 2 (fun k => 7 + k)))) (mem 0 5))))))))))
def outputRoot (P H : Form) : Form := .all (.ex (.conj (.impl (subst P shift) (mem 1 0)) (subst H (up shift))))
def seedRoot (P H : Form) : Form := .ex (.conj (.impl (subst (.ex P) shift) (.ex (.conj (mem 0 1) (subst P (up shift))))) H)
def kprimeCore (φ : Form) : Form := .all (outputRoot φ (emittedClosure φ))
inductive KPrimeOrd : Form → Prop where
  | eq {φ : Form} : φ ∈ equalityAxioms → KPrimeOrd φ
  | instance (φ : Form) (n : Nat) : closedf (forallTimes n (kprimeCore φ)) → KPrimeOrd (forallTimes n (kprimeCore φ))
def irreflexivity : Form := .all (neg (mem 0 0))
def KPrimeOrdIR (φ : Form) : Prop := KPrimeOrd φ ∨ φ = irreflexivity
end K230


