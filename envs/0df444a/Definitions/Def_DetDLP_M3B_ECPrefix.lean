-- Prove2me | Definitions.Def_DetDLP_M3B_ECPrefix
-- name    : DetDLP_M3B_ECPrefix
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:46:03.762342+00:00
-- url     : https://prove2.me/theorems/8e9bbbb3-8403-4230-a285-3ab571672d7d
-- title:
--   Exact EC separator prefix pin wiring
-- statement:
--   Constructs finite-point tag and coordinate prefix references and proves the pin block checks precisely the native separator tuple-word prefix, including overlong inputs.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECArithNet

set_option autoImplicit false
namespace DetDLP.M3B.ECPrefix
open S8H0.RegisterMap S8H0.NamedBlocks ECCert ECArithNet S8H.ECPointArithmetic

variable {r : Shape} {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (F : Fin m → List (Point E)) (S : ECSeed p m) (T : ℕ) (mul : w3_modMulInterface)
variable (hT : T ≤ p) (hF : ListsOK E F S T)

/-- The native separator serializes the infinity tag as a whole word. All
    accepted factor-base slots are finite, so that word can be public zeroes. -/
def one {b : ℕ} (x y : Fin b → Ref r) :=
  List.replicate b (Ref.pin false) ++ List.ofFn x ++ List.ofFn y

theorem one_correct (i : Fin m) (w : Slot E S T i) (a : Fin (r.size+1) → Bool)
    (x y : Fin (bitLen p) → Ref r)
    (hx : ∀ j, (x j).eval a = w.1.1.2.1.val.testBit j.val)
    (hy : ∀ j, (y j).eval a = w.1.1.2.2.val.testBit j.val) :
    (one x y).map (fun v => v.eval a) =
    (pointCoords ((F i).get (indexEquiv E F S T mul hT hF i w))).flatMap (w3_bits (bitLen p)) := by
  have hc := ECAddress.coords_get E S T i F mul hT hF w
  have hn := (ECAddress.slot_semantics E S T i w).2.2.1
  generalize he : (F i).get (indexEquiv E F S T mul hT hF i w) = P at hc ⊢
  cases P with
  | zero => have hh := congrArg Prod.fst hc; simp [coords,hn] at hh
  | some X Y h =>
    have ex : X = w.1.1.2.1 := congrArg (fun c => c.2.1) hc
    have ey : Y = w.1.1.2.2 := congrArg (fun c => c.2.2) hc
    subst X; subst Y
    have hz : (Ref.pin (s:=r) false).eval a = false := rfl
    simp [one,List.map_ofFn,Function.comp_def,hx,hy,pointCoords,w3_bits,hz]

abbrev Route (r : Shape) (m b : ℕ) := Bool → Fin m → Fin 2 → Fin b → Ref r

def side {b : ℕ} (x y : Route r m b) (s : Bool) :=
  (List.finRange m).flatMap fun i => (List.finRange 2).flatMap fun j => one (x s i j) (y s i j)

def refs {b : ℕ} (x y : Route r m b) := side x y false ++ side x y true

theorem refs_correct (x y : Route r m (bitLen p)) (a : Fin (r.size+1) → Bool) (w : Table E S T)
    (hx : ∀ s i j l, (x s i j l).eval a = (w i j s).1.1.2.1.val.testBit l.val)
    (hy : ∀ s i j l, (y s i j l).eval a = (w i j s).1.1.2.2.val.testBit l.val) :
    let t := tableEquiv E F S T mul hT hF w
    (refs x y).map (fun v => v.eval a) = w3_tupleWord (base E F)
      (fun A => (pointCoords A).flatMap (w3_bits (bitLen p))) t.1 t.2 := by
  have H (s : Bool) (i : Fin m) (j : Fin 2) := one_correct E F S T mul hT hF i (w i j s) a
    (x s i j) (y s i j) (hx s i j) (hy s i j)
  simp only [refs,side,List.map_append,List.map_flatMap,Function.comp_def,H,w3_tupleWord,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

theorem prefix_correct (x y : Route r m (bitLen p)) (a : Fin (r.size+1) → Bool) (w : Table E S T)
    (hx : ∀ s i j l, (x s i j l).eval a = (w i j s).1.1.2.1.val.testBit l.val)
    (hy : ∀ s i j l, (y s i j l).eval a = (w i j s).1.1.2.2.val.testBit l.val) (pre : List Bool) :
    (prefixBlock (refs x y) pre).OK a ↔ prefixOK E F pre (tableEquiv E F S T mul hT hF w) := by
  rw [prefix_iff,refs_correct E F S T mul hT hF x y a w hx hy]; rfl

end DetDLP.M3B.ECPrefix


