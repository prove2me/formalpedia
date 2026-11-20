-- Prove2me | Definitions.Def_DualSepClusterLP_TriangleCertificateChecker
-- name    : DualSepClusterLP_TriangleCertificateChecker
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T12:39:30.05527+00:00
-- url     : https://prove2.me/theorems/2728df98-5ad3-4bdd-9aea-29eb7c94d6ca
-- title:
--   Exact certificate checker for Cluster LP triangle rounding
-- statement:
--   Definitions of the degree-eleven Bernstein checker and the simplex cover checker for the triangle inequalities in Lemma 7.3. An accepted certificate covers a whole domain by rational simplices and checks the signs of all polynomial coefficients with integer arithmetic.
-- source:
--   García-Soriano and Schohn, Approximate Dual Separation for the Cluster LP, Lemma 7.3 and Appendix C. https://arxiv.org/abs/2607.27829

import Definitions.Def_DualSepClusterLP_RoundingAnalysis

namespace DualSepClusterLP.TriCert

open Lean.Grind.CommRing

abbrev E := Lean.Grind.CommRing.Expr

def isPos (k : ℕ) : Bool := decide (k < 3)

noncomputable def lo (k : ℕ) : ℝ := if k = 1 ∨ k = 4 then 1/2 else if k = 2 then 25/26 else 0

noncomputable def hi (k : ℕ) : ℝ := if k = 0 ∨ k = 3 then 1/2 else if k = 1 then 25/26 else 1

def OnPiece (k : ℕ) (x : ℝ) : Prop := x ∈ Set.Icc (lo k) (hi k)

noncomputable def choose (s : Bool) (x : ℝ) : ℕ :=
  if s then if x ≤ 1/2 then 0 else if x ≤ 25/26 then 1 else 2
  else if x ≤ 1/2 then 3 else 4

section

variable {A : Type} [∀ n : ℕ, OfNat A n] [Add A] [Sub A] [Mul A] [Pow A ℕ]

def meanN (k : ℕ) (x l : A) : A :=
  match k with
  | 0 => 12*x*l
  | 1 => 12*x*l + (l-x)*(13*(2*x-l))
  | 2 => 12*l^2
  | 3 => 18*x*l
  | _ => 12*(2*x*l-x^2)

def gammaN (k : ℕ) (x l : A) : A :=
  match k with
  | 0 => 12*l
  | 1 => 12*l-13*(2*x-l)
  | _ => 0

def shapeN (k : ℕ) (x l : A) : A := if isPos k then x*(l-x)^2 else 0

def budgetN (k : ℕ) (x l : A) : A := if isPos k then 2*(l-x)^2 else x*(3*l-2*x)

def pivotN (a b c : ℕ) (x y z t l : A) : A :=
  let m := meanN a x l
  let n := meanN b y l
  let cov := t*l-x*y
  let j := m*n+gammaN a x l*gammaN b y l*cov
  let u := (m+n)*(12*l^2)
  let d := (2*l-x)*(2*l-y)*(2*l-z)
  25*2773*l^3*(u-j)*budgetN c z l*(2*l-x)*(2*l-y) -
    25*1227*l^4*(if isPos c then u-2*j else j)*d -
    2024*144*1227*shapeN a x l*shapeN b y l*cov*d

def homTriangle (a b c : ℕ) (x y z t l : A) : A :=
  pivotN a c b x z y t l + pivotN b a c y x z t l + pivotN c b a z y x t l

end

instance : Add E := ⟨.add⟩

instance : Sub E := ⟨.sub⟩

instance : Mul E := ⟨.mul⟩

instance : Pow E ℕ := ⟨.pow⟩

instance (n : ℕ) : OfNat E n := ⟨.natCast n⟩

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriGeo

structure Form where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Inhabited, Repr

def Form.eval (q : Form) (x y z : ℝ) : ℝ := q.a*x + q.b*y + q.c*z + q.d

def Form.mix (q : Form) (a b c d : ℝ) : ℝ := q.a*a + q.b*b + q.c*c + q.d*d

def Form.add (q r : Form) : Form := ⟨q.a+r.a,q.b+r.b,q.c+r.c,q.d+r.d⟩

def Form.sub (q r : Form) : Form := ⟨q.a-r.a,q.b-r.b,q.c-r.c,q.d-r.d⟩

def Form.scale (k : ℤ) (q : Form) : Form := ⟨k*q.a,k*q.b,k*q.c,k*q.d⟩

def zeroF : Form := ⟨0,0,0,0⟩

def oneF : Form := ⟨0,0,0,1⟩

def xF : Form := ⟨1,0,0,0⟩

def yF : Form := ⟨0,1,0,0⟩

def zF : Form := ⟨0,0,1,0⟩

structure Tet where
  den : ℕ
  X : Form
  Y : Form
  Z : Form
deriving DecidableEq, Inhabited, Repr

def OnTet (p : ℝ → ℝ → ℝ → Prop) (s : Tet) : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a+b+c+d=1 →
  p (s.X.mix a b c d/s.den) (s.Y.mix a b c d/s.den) (s.Z.mix a b c d/s.den)

structure Frame where
  den : ℕ
  A : Form
  B : Form
  C : Form
  D : Form
deriving DecidableEq, Inhabited, Repr

def Frame.lin (f : Frame) (q : Form) : Form :=
  (((f.A.scale q.a).add (f.B.scale q.b)).add (f.C.scale q.c)).add (f.D.scale q.d)

def Frame.massDiff (f : Frame) : Form := (((f.A.add f.B).add f.C).add f.D).sub (oneF.scale f.den)

def Frame.coordDiff (f : Frame) (s : Tet) (q var : Form) : Form :=
  (f.lin q).sub (var.scale (f.den*s.den : ℕ))

def opp (q : Form) : Form := q.scale (-1)

def Frame.requirements (f : Frame) (s : Tet) : List Form :=
  let m := f.massDiff
  let x := f.coordDiff s s.X xF
  let y := f.coordDiff s s.Y yF
  let z := f.coordDiff s s.Z zF
  [f.A,f.B,f.C,f.D,m,opp m,x,opp x,y,opp y,z,opp z]

def Satisfies (xs : List Form) (x y z : ℝ) : Prop := ∀ q ∈ xs, 0 ≤ q.eval x y z

abbrev Coeff := ℕ × ℕ

def combination (cs : List Form) : List Coeff → Form
  | [] => zeroF
  | (i,k)::t => ((cs[i]?.getD zeroF).scale k).add (combination cs t)

structure Derivation where
  mul : ℕ
  terms : List Coeff
deriving Repr, Inhabited

def Derivation.valid (cs : List Form) (q : Form) (p : Derivation) : Bool :=
  decide (0 < p.mul ∧ q.scale p.mul = combination cs p.terms)

def allDerivable (cs : List Form) : List Form → List Derivation → Bool
  | [], [] => true
  | q::qs,p::ps => p.valid cs q && allDerivable cs qs ps
  | _,_ => false

inductive Cover where
  | cut (q : Form) (pos neg : Cover)
  | leaf (index : ℕ) (proofs : List Derivation)
  | empty (proof : Derivation)
deriving Repr, Inhabited

abbrev Tile := Tet × Frame

def Cover.check (tiles : Array Tile) (cs : List Form) : Cover → Bool
  | .cut q pos neg => pos.check tiles (q::cs) && neg.check tiles (opp q::cs)
  | .empty pr => pr.valid cs (opp oneF)
  | .leaf i proofs =>
    match tiles[i]? with
    | none => false
    | some (s,f) => decide (0 < s.den ∧ 0 < f.den) && allDerivable cs (f.requirements s) proofs

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriGeo

def InRegion (k : ℕ) (x y z : ℝ) : Prop :=
  match k with
  | 0 => 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x+y+z ≤ 1
  | 1 => 1 ≤ x+y+z ∧ x+y ≤ 1 ∧ x+z ≤ 1 ∧ y+z ≤ 1
  | 2 => 1 ≤ x+y ∧ z ≤ x ∧ z ≤ y ∧ x+y-z ≤ 1
  | 3 => 1 ≤ x+z ∧ y ≤ x ∧ y ≤ z ∧ x+z-y ≤ 1
  | 4 => 1 ≤ y+z ∧ x ≤ y ∧ x ≤ z ∧ y+z-x ≤ 1
  | 5 => 0 ≤ x ∧ x ≤ y ∧ x ≤ z ∧ y+z-x ≤ 1
  | 6 => 0 ≤ y ∧ y ≤ x ∧ y ≤ z ∧ x+z-y ≤ 1
  | _ => 0 ≤ z ∧ z ≤ x ∧ z ≤ y ∧ x+y-z ≤ 1

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriGeo

open TriCert

def AxisX (k : ℕ) : List Form :=
  match k with
  | 0 => [⟨-2,0,0,1⟩,⟨1,0,0,0⟩]
  | 1 => [⟨-26,0,0,25⟩,⟨2,0,0,-1⟩]
  | 2 => [⟨-1,0,0,1⟩,⟨26,0,0,-25⟩]
  | 3 => [⟨-2,0,0,1⟩,⟨1,0,0,0⟩]
  | _ => [⟨-1,0,0,1⟩,⟨2,0,0,-1⟩]

def AxisY (k : ℕ) : List Form :=
  match k with
  | 0 => [⟨0,-2,0,1⟩,⟨0,1,0,0⟩]
  | 1 => [⟨0,-26,0,25⟩,⟨0,2,0,-1⟩]
  | 2 => [⟨0,-1,0,1⟩,⟨0,26,0,-25⟩]
  | 3 => [⟨0,-2,0,1⟩,⟨0,1,0,0⟩]
  | _ => [⟨0,-1,0,1⟩,⟨0,2,0,-1⟩]

def AxisZ (k : ℕ) : List Form :=
  match k with
  | 0 => [⟨0,0,-2,1⟩,⟨0,0,1,0⟩]
  | 1 => [⟨0,0,-26,25⟩,⟨0,0,2,-1⟩]
  | 2 => [⟨0,0,-1,1⟩,⟨0,0,26,-25⟩]
  | 3 => [⟨0,0,-2,1⟩,⟨0,0,1,0⟩]
  | _ => [⟨0,0,-1,1⟩,⟨0,0,2,-1⟩]

def RegionForms (e : ℕ) : List Form := match e with
  | 0 => [⟨-1,-1,-1,1⟩,⟨0,0,1,0⟩,⟨0,1,0,0⟩,⟨1,0,0,0⟩]
  | 1 => [⟨0,-1,-1,1⟩,⟨-1,0,-1,1⟩,⟨-1,-1,0,1⟩,⟨1,1,1,-1⟩]
  | 2 => [⟨-1,-1,1,1⟩,⟨0,1,-1,0⟩,⟨1,0,-1,0⟩,⟨1,1,0,-1⟩]
  | 3 => [⟨-1,1,-1,1⟩,⟨0,-1,1,0⟩,⟨1,-1,0,0⟩,⟨1,0,1,-1⟩]
  | 4 => [⟨1,-1,-1,1⟩,⟨-1,0,1,0⟩,⟨-1,1,0,0⟩,⟨0,1,1,-1⟩]
  | 5 => [⟨1,-1,-1,1⟩,⟨-1,0,1,0⟩,⟨-1,1,0,0⟩,⟨1,0,0,0⟩]
  | 6 => [⟨-1,1,-1,1⟩,⟨0,-1,1,0⟩,⟨1,-1,0,0⟩,⟨0,1,0,0⟩]
  | _ => [⟨-1,-1,1,1⟩,⟨0,1,-1,0⟩,⟨1,0,-1,0⟩,⟨0,0,1,0⟩]

def AllForms (a b c e : ℕ) : List Form :=
  RegionForms e ++ AxisZ c ++ AxisY b ++ AxisX a ++ [oneF]

end DualSepClusterLP.TriGeo

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

def ctx4 (a b c d : ℝ) : Context ℝ := .branch 2 (.branch 1 (.leaf a) (.leaf b))
    (.branch 3 (.leaf c) (.leaf d))

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TrianglePacking

def slot (i j k : Nat) : Nat := i + 67*j + 79*k

def weight : Fin 4 → ℕ := ![0,1,67,79]

end DualSepClusterLP.TrianglePacking

namespace DualSepClusterLP.TriBern

def guardMask (k n : ℕ) : ℕ :=
  2^k * ((2^((k+1)*n)-1) / (2^(k+1)-1))

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open MvPolynomial

open DualSepClusterLP.TrianglePacking

abbrev Poly4 := MvPolynomial (Fin 4) ℤ

abbrev Exp4 := Fin 4 →₀ ℕ

def code (e : Exp4) : ℕ := ∑ i, e i * weight i

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TrianglePacking

open MvPolynomial

abbrev PE := Lean.Grind.CommRing.Expr

abbrev ZP := MvPolynomial (Fin 4) ℤ

abbrev NP := MvPolynomial (Fin 4) ℕ

noncomputable def toMv : PE → ZP
  | .num z | .intCast z => C z
  | .natCast n => C (n:ℤ)
  | .var i => X ⟨min i 3, by omega⟩
  | .neg a => -toMv a
  | .add a b => toMv a + toMv b
  | .sub a b => toMv a - toMv b
  | .mul a b => toMv a * toMv b
  | .pow a n => toMv a ^ n

def bound : PE → ℕ
  | .num z | .intCast z => z.natAbs
  | .natCast n => n
  | .var _ => 1
  | .neg a => bound a
  | .add a b | .sub a b => bound a + bound b
  | .mul a b => bound a * bound b
  | .pow a n => bound a ^ n

inductive G where
  | bad | zero | deg (n : ℕ)
  deriving DecidableEq, Repr

def G.plus : G → G → G
  | .zero, b => b
  | a, .zero => a
  | .deg n, .deg m => if n=m then .deg n else .bad
  | _,_ => .bad

def G.times : G → G → G
  | .zero,_ | _,.zero => .zero
  | .deg n,.deg m => .deg (n+m)
  | _,_ => .bad

def G.power (a : G) (n : ℕ) : G :=
  if n=0 then .deg 0 else match a with
    | .deg m => .deg (m*n)
    | .zero => .zero
    | .bad => .bad

def grade : PE → G
  | .num z | .intCast z => if z=0 then .zero else .deg 0
  | .natCast n => if n=0 then .zero else .deg 0
  | .var _ => .deg 1
  | .neg a => grade a
  | .add a b | .sub a b => (grade a).plus (grade b)
  | .mul a b => (grade a).times (grade b)
  | .pow a n => (grade a).power n

end DualSepClusterLP.TrianglePacking

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

def index4 (i : ℕ) : Fin 4 := ⟨min i 3, by omega⟩

def ringValue {R : Type*} [CommRing R] (x : ℕ → R) : Expr → R
  | .num k | .intCast k => k
  | .natCast n => n
  | .var i => x i
  | .neg a => -ringValue x a
  | .add a b => ringValue x a + ringValue x b
  | .sub a b => ringValue x a - ringValue x b
  | .mul a b => ringValue x a * ringValue x b
  | .pow a n => ringValue x a ^ n

def packedValue (e : Expr) : ℤ :=
  ringValue (fun i => ((2:ℤ)^(240 * weight (index4 i)))) e

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

def packedOK (e : Expr) : Bool :=
  let g := grade e
  let v := packedValue e
  decide (g = .zero ∨ g = .deg 11) &&
    decide (bound e < 2^239) && decide (0 ≤ v) &&
    decide (v.toNat &&& guardMask 239 870 = 0)

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriBern

open Lean.Grind.CommRing

open DualSepClusterLP.TrianglePacking

end DualSepClusterLP.TriBern

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

def endForm {A : Type} [Sub A] [Add A] [OfNat A 0] (ep : ℕ) (x y z l : A) : A :=
  match ep with
  | 0 => 0 | 1 => x+y-l | 2 => x+z-l | 3 => y+z-l
  | 4 => x | 5 => y | _ => z

def endpointValue (ep : ℕ) (x y z : ℝ) : ℝ := endForm ep x y z 1

def readForm (q : Form) : E :=
  (.intCast q.a : E)*(.var 0)+(.intCast q.b : E)*(.var 1)+
  (.intCast q.c : E)*(.var 2)+(.intCast q.d : E)*(.var 3)

def totalForm (s : Tet) : E := (.natCast s.den : E) *
  ((.var 0 : E)+(.var 1 : E)+(.var 2 : E)+(.var 3 : E))

def tileExpr (a b c ep : ℕ) (s : Tet) : E :=
  let x := readForm s.X
  let y := readForm s.Y
  let z := readForm s.Z
  let l := totalForm s
  homTriangle a b c x y z (endForm ep x y z l) l

def certificateProperty (a b c ep : ℕ) (x y z : ℝ) : Prop :=
  OnPiece a x → OnPiece b y → OnPiece c z →
  0 ≤ signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z (endpointValue ep x y z)

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

def Ends (a b c : ℕ) (x y z : ℝ) : Prop :=
  tripleLower x y z ≤ tripleUpper x y z →
    0 ≤ signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus (isPos a) (isPos b) (isPos c) x y z (tripleUpper x y z)

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

def validTiles (a b c ep : ℕ) (tiles : Array Tile) : Bool :=
  tiles.all (fun q => decide (0 < q.1.den) && packedOK (tileExpr a b c ep q.1))

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert

open TriGeo TriBern

end DualSepClusterLP.TriCert

namespace DualSepClusterLP.TriCert
open TriGeo
structure RegionCertificate where
  tiles : Array Tile
  cover : Cover
deriving Inhabited

def regionOK (a b c : ℕ) (e : Fin 8) (tab : RegionCertificate) : Bool :=
  tab.cover.check tab.tiles (AllForms a b c e) && validTiles a b c (e.val-1) tab.tiles

def acceptsBox (a b c : ℕ) (regions : Fin 8 → RegionCertificate) : Bool :=
  decide (∀ e : Fin 8, regionOK a b c e (regions e) = true)

/-- The finite cover and its independently checked acceptance on all eight endpoint regions. -/
structure CertifiedBox (a b c : ℕ) where
  regions : Fin 8 → RegionCertificate
  accepted : acceptsBox a b c regions = true
end DualSepClusterLP.TriCert


