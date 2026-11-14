-- Prove2me | Definitions.Def_APFPaper5_K3_CarrierFrame
-- name    : APFPaper5_K3_CarrierFrame
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:52:26.830197+00:00
-- url     : https://prove2.me/theorems/34ad7761-6a49-495c-9db9-a992a3d1f4f4
-- title:
--   Carrier-frame conditions and coordinate maps
-- statement:
--   Defines a real vector space frame with a symmetric bilinear form, linear isometric J with square minus identity, two orthonormal complex directions and full four-coordinate spanning; defines its coordinate maps and a concrete coordinate witness. The checklist is a supplied conjunction, not a derivation of a physical carrier. J and full spanning are substantive structural conditions.
--
--   **Meaning and scope.** Faithful as the stated mathematical encoding with this exposure: The checklist is a supplied conjunction, not a derivation of a physical carrier. J and full spanning are substantive structural conditions.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K3.frameMap', 'statement_and_binders': 'def frameMap (J : V → V) (a b : V) (h : Held2) : V'}
--   - {'declaration': 'APFPaper5.K3.frameCoords', 'statement_and_binders': 'def frameCoords (B : V → V → ℝ) (J : V → V) (a b : V) (v : V) : Held2'}
--   - {'declaration': 'APFPaper5.K3.pullback', 'statement_and_binders': 'def pullback (B : V → V → ℝ) (J : V → V) (a b : V) (T : V → V) (h : Held2) : Held2'}
--   - {'declaration': 'APFPaper5.K3.IsTwoComponentCarrier', 'statement_and_binders': 'def IsTwoComponentCarrier (B : V → V → ℝ) (J : V → V) (a b : V) : Prop'}
--   - {'declaration': 'APFPaper5.K3.coordCross', 'statement_and_binders': 'def coordCross (x y : ℝ × ℝ × ℝ × ℝ) : ℝ'}
--   - {'declaration': 'APFPaper5.K3.coordQuarter', 'statement_and_binders': 'def coordQuarter (x : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ'}
--
--   **Limits**
--
--   - Q44-01
--   - Q44-02
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_CarrierFrame.lean; Sib v44 / pullbacks v1, SHA-256 405aaea23ce7107391b81ec864694b9d80bb06a6c8e8e8fecdb9c69f926d894f. {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}; {'path': 'source/Definitions/Def_APFPaper5_K3_CarrierFrame.lean', 'sha256': '405aaea23ce7107391b81ec864694b9d80bb06a6c8e8e8fecdb9c69f926d894f'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_CarrierFrame
title: The checklist that makes a space of held states a carrier of two held components, and its reading in values and rates
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:1618-1705 (the occupied smooth recombining Held germ; first-jet rank two),
 1800-1840 (common phase record-null, relative phase retained by recombination). The adopted clauses
 RECORDS, PRESERVATION, CONTINUITY; the named hypothesis FIRST-ORDER.
standing: a TYPED LIST OF CONDITIONS, not a declared input and not an adopted clause. It says what an
 interface has to supply for the model of two held components to apply to it.
statement: B is the cross term of cost on held states, J the quarter turn, a and b one held state of each
 component. IsTwoComponentCarrier B J a b says: B is additive and homogeneous in each argument and symmetric;
 J is additive and homogeneous, done twice it reverses, and it leaves B unchanged; a and b have unit cost;
 the cross terms of a with b and with the quarter turn of b vanish; every held state is a combination of a,
 its quarter turn, b and its quarter turn. frameMap J a b h is the held state with the values and rates h.
 frameCoords B J a b v reads the values and rates of v as cross terms of cost. pullback B J a b T is the map
 T of held states read in values and rates. coordCross and coordQuarter are the cross term of cost and the
 quarter turn on four real coordinates, used to show that the checklist can be met.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K3_HeldMaps

set_option autoImplicit false
namespace APFPaper5.K3

open APFPaper5.K1

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The held state with given values and rates of the two components. -/
def frameMap (J : V → V) (a b : V) (h : Held2) : V :=
  h.a1 • a + h.a2 • J a + h.b1 • b + h.b2 • J b

/-- The values and rates of a held state, read as cross terms of cost. -/
def frameCoords (B : V → V → ℝ) (J : V → V) (a b : V) (v : V) : Held2 :=
  ⟨B a v, B (J a) v, B b v, B (J b) v⟩

/-- A map of held states, read in values and rates. -/
def pullback (B : V → V → ℝ) (J : V → V) (a b : V) (T : V → V) (h : Held2) : Held2 :=
  frameCoords B J a b (T (frameMap J a b h))

/-- What makes a space of held states a carrier of two held components. -/
def IsTwoComponentCarrier (B : V → V → ℝ) (J : V → V) (a b : V) : Prop :=
  IsBilinear B ∧ (∀ x y : V, B x y = B y x) ∧
  (∀ x y : V, J (x + y) = J x + J y) ∧ (∀ (r : ℝ) (x : V), J (r • x) = r • J x) ∧
  (∀ x : V, J (J x) = -x) ∧ (∀ x y : V, B (J x) (J y) = B x y) ∧
  B a a = 1 ∧ B b b = 1 ∧ B a b = 0 ∧ B a (J b) = 0 ∧
  ∀ v : V, ∃ x y z w : ℝ, v = x • a + y • J a + z • b + w • J b

/-- The cross term of cost on four real coordinates. -/
def coordCross (x y : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2.1 * y.2.2.1 + x.2.2.2 * y.2.2.2

/-- The quarter turn on four real coordinates. -/
def coordQuarter (x : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ := (-x.2.1, x.1, -x.2.2.2, x.2.2.1)

end APFPaper5.K3


