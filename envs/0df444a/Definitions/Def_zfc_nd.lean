-- Prove2me | Definitions.Def_zfc_nd
-- name    : zfc_nd
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T22:32:52.003316+00:00
-- url     : https://prove2.me/theorems/4a34a8e2-6483-49f6-9149-350ee4b01d85
-- title:
--   Natural deduction and the ZFC axiom set
-- statement:
--   Natural-deduction derivability for set theory and the concrete ZFC axiom set (twelve fixed axioms plus Separation and Replacement instances), with the provability predicate `zfcProvable` and `zfcInconsistent`. Transcribed from `pa-mm0/source_nd_prop.mm0`, `source_nd_quantifiers.mm0`, `zfc_fixed.mm0`, `zfc_schemas.mm0`, `zfc_schema_maps.mm0`, `zfc_axioms.mm0`, `zfc_proofs.mm0`.
-- source:
--   https://github.com/elliotglazer/k215-pa (pa-mm0/zfc_proofs.mm0)

import Definitions.Def_set_formula

namespace K215

inductive ND : List SFormula → SFormula → Prop where
  | ctx {G a} : a ∈ G → ND G a
  | pc {G a b} : ND G (.imp (.imp (.imp a b) a) a)
  | ii {G a b} : ND (a :: G) b → ND G (.imp a b)
  | exp {G a} : ND G .bot → ND G a
  | ce1 {G a b} : ND G (.and a b) → ND G a
  | ce2 {G a b} : ND G (.and a b) → ND G b
  | di1 {G a b} : ND G a → ND G (.or a b)
  | di2 {G a b} : ND G b → ND G (.or a b)
  | ie {G a b} : ND G (.imp a b) → ND G a → ND G b
  | ci {G a b} : ND G a → ND G b → ND G (.and a b)
  | de {G a b c} : ND G (.or a b) → ND (a :: G) c → ND (b :: G) c → ND G c
  | wk {G H a} : ND G a → (∀ x, x ∈ G → x ∈ H) → ND H a
  | allI {G a} : ND (contextShift G) a → ND G (.all a)
  | allE {G a t} : ND G (.all a) → ND G (subst 0 t a)
  | exI {G a t} : ND G (subst 0 t a) → ND G (.ex a)
  | exE {G a c} : ND G (.ex a) → ND (a :: contextShift G) (shift 0 c) → ND G c

def iff (a b : SFormula) : SFormula := .and (.imp a b) (.imp b a)
def separation (body : SFormula) : SFormula := .all (.ex (.all (iff (.mem 0 1) (.and (.mem 0 2) body))))
def functionality (bodyA bodyB : SFormula) : SFormula := .all (.all (.all (.imp bodyA (.imp bodyB (.eq 1 0)))))
def replacement (bodyA bodyB bodyC : SFormula) : SFormula := .imp (functionality bodyA bodyB) (.all (.ex (.all (iff (.mem 0 1) (.ex (.and (.mem 0 3) bodyC))))))
def allPrefix : Nat → SFormula → SFormula
  | 0, c => c
  | n + 1, c => .all (allPrefix n c)
def sepIndex (i : Nat) : Nat := if i = 0 then 0 else i + 2
def repAIndex (i : Nat) : Nat := if i = 0 then 2 else if i = 1 then 1 else i + 1
def repBIndex (i : Nat) : Nat := if i = 0 then 2 else if i = 1 then 0 else i + 1
def repCIndex (i : Nat) : Nat := if i = 0 then 0 else if i = 1 then 1 else i + 2
def separationCode (phi : SFormula) (n : Nat) : SFormula := allPrefix n (separation (rename sepIndex 0 phi))
def replacementCode (phi : SFormula) (n : Nat) : SFormula := allPrefix n (replacement (rename repAIndex 0 phi) (rename repBIndex 0 phi) (rename repCIndex 0 phi))
def zfcRefl : SFormula := .all (.eq 0 0)
def zfcSym : SFormula := .all (.all (.imp (.eq 1 0) (.eq 0 1)))
def zfcTrans : SFormula := .all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0)))))
def zfcEqElem : SFormula := .all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0)))))))
def zfcExt : SFormula := .all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0))))
def zfcEmpty : SFormula := .ex (.all (.imp (.mem 0 1) (.bot)))
def zfcPair : SFormula := .all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1))))))
def zfcUnion : SFormula := .all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1)))))
def zfcPower : SFormula := .all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1)))))
def zfcOmega : SFormula := .ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1))))))
def zfcFoundation : SFormula := .all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot)))))))
def zfcChoice : SFormula := .all (.imp (.all (.imp (.mem 0 1) (.ex (.mem 0 1)))) (.imp (.all (.imp (.mem 0 1) (.all (.imp (.mem 0 2) (.imp (.imp (.eq 1 0) (.bot)) (.imp (.ex (.and (.mem 0 2) (.mem 0 1))) (.bot))))))) (.ex (.all (.imp (.mem 0 2) (.ex (.and (.and (.mem 0 1) (.mem 0 2)) (.all (.imp (.mem 0 2) (.imp (.mem 0 3) (.eq 0 1)))))))))))
def zfcFixed (z : SFormula) : Prop := z ∈ [zfcRefl, zfcSym, zfcTrans, zfcEqElem, zfcExt, zfcEmpty, zfcPair, zfcUnion, zfcPower, zfcOmega, zfcFoundation, zfcChoice]
def zfcClosedSeparation (z : SFormula) : Prop := bound 0 z ∧ ∃ (phi : SFormula) (n : Nat), bound (n + 1) phi ∧ z = separationCode phi n
def zfcClosedReplacement (z : SFormula) : Prop := bound 0 z ∧ ∃ (phi : SFormula) (n : Nat), bound (n + 2) phi ∧ z = replacementCode phi n
def zfcAxioms (z : SFormula) : Prop := zfcFixed z ∨ zfcClosedSeparation z ∨ zfcClosedReplacement z
def zfcProvable (f : SFormula) : Prop := ∃ G : List SFormula, (∀ a, a ∈ G → zfcAxioms a) ∧ ND G f
def zfcInconsistent : Prop := zfcProvable .bot

end K215


