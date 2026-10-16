-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
-- name    : OAI_MathematicalPhysics_SheetFlows_Circuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:27:17.510022+00:00
-- url     : https://prove2.me/theorems/62c066ef-e3ed-48ec-bc64-55800da364c8
-- title:
--   Arithmetic circuits with flat-function atoms, encoded by partial recursive codes
-- statement:
--   This file introduces arithmetic circuits on space-time $\mathbb{R}\times\mathbb{R}^3$ together with their real values, rational ball approximations, magnitude bounds and symbolic derivatives. Space-time points are $z=(t,x)$, with coordinates $z_0=t$, $z_1=x_0$, $z_2=x_1$, $z_3=x_2$. Write $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$; the flat monomials are $F_m(s)=s^{-m}\psi(s)$ for $s>0$ and $F_m(s)=0$ for $s\le0$ ($m\in\mathbb{N}$); and $R(s)=1/\bigl(\psi(s)+\psi(1-s)\bigr)$. A rational ball $(c,r)\in\mathbb{Q}^2$ stands for the interval $[c-r,c+r]$; balls are added by adding centers and radii and multiplied by $(c_1,r_1)\otimes(c_2,r_2)=(c_1c_2,\,|c_1|r_2+|c_2|r_1+r_1r_2)$.
--
--   1. **Atoms.** An atom is a quadruple $(j,a,b,k)$ with $j\in\{0,1,2,3\}$, $a,b\in\mathbb{Q}$ and $k\in\mathbb{N}$. Its profile is $P_0(s)=s$, $P_1=R$, and $P_k=F_{k-2}$ for $k\ge2$, and its value at $z$ is
--   $$(j,a,b,k)(z)=P_k(a\,z_j+b).$$
--   At a rational point $q\in\mathbb{Q}^4$ its argument is the rational number $aq_j+b$. Its ball approximation at precision $n$ is the exact point ball of the argument if $k=0$, the rational ball enclosure of $R$ at the argument if $k=1$, and the rational ball enclosure of $F_{k-2}$ at the argument if $k\ge2$. Its magnitude bound for radius $\rho\in\mathbb{Q}$ is $|a|\,|\rho|+|b|$ if $k=0$, $16$ if $k=1$, and $(k-2)!$ if $k\ge2$.
--   2. **Circuits.** Circuits are the codes of partial recursive functions, reinterpreted as arithmetic formulas: a pairing code $\langle C,D\rangle$ stands for the sum $C+D$, a composition code $C\circ D$ for the product $CD$, a primitive-recursion code with first component $c$ for the atom decoded from $c$, an unbounded-search code with component $c$ for the rational constant decoded from $c$, and the four basic codes (zero, successor, left and right projection) for the constant $0$. Accordingly every circuit $C$ has a real value $C(z)$; a ball approximation $\mathrm{approx}(C,q,n)$ at rational points $q\in\mathbb{Q}^4$, obtained with ball addition and multiplication from the atom approximations and the point balls of constants; and a rational magnitude bound $\mathrm{bound}(C,\rho)$, obtained by adding and multiplying the atom bounds and the absolute values $|q|$ of constants. The constructors $\mathrm{const}(q)$, $\mathrm{atom}(j,a,b,k)$, $C+D$, $CD$ and $C-D=C+(-1)D$ produce circuits with values $q$, $P_k(az_j+b)$, $C(z)+D(z)$, $C(z)D(z)$ and $C(z)-D(z)$. A rational point $q\in\mathbb{Q}^4$ is identified with the space-time point $(q_0,(q_1,q_2,q_3))$.
--   3. **Symbolic derivatives.** Using the profile derivatives
--   $$P_0'=1,\qquad P_1'(s)=-R(s)^2\bigl(F_2(s)-F_2(1-s)\bigr),\qquad F_m'=F_{m+2}-m\,F_{m+1},$$
--   the partial derivative of the atom $(j,a,b,k)$ in the coordinate $z_i$ is the circuit for $a\,P_k'(az_j+b)$ if $i=j$ and the constant $0$ otherwise; the term $F_2(1-s)$ is realized by the reflected atom with parameters $(j,-a,1-b)$, whose argument is $1-(az_j+b)$. This extends to all circuits by the sum and product rules, giving $\partial_iC$, and to mixed derivatives $\partial^{\alpha}C=\partial_{j_1}(\partial_{j_2}(\cdots\partial_{j_k}C))$ for lists $\alpha=(j_1,\dots,j_k)$ of coordinate indices (the last index acts first).
--   4. **Fields and sums.** A triple $(C_0,C_1,C_2)$ of circuits defines the vector field $u(t,x)=\bigl(C_0(t,x),C_1(t,x),C_2(t,x)\bigr)$; finite sums of circuits over lists and over finite index types are formed by iterated addition, starting from the constant $0$.
--   5. **Compilation.** A polynomial $p=\sum_n c_nX^n\in\mathbb{Q}[X]$ yields the circuit $\sum_{n}c_n\,\mathrm{atom}(j,a,b,n+2)$, whose value is $p(1/s)\psi(s)$ at $s=az_j+b$ (and $0$ if $s\le0$). A one-variable jet expression $e$ (a formal expression built from rational constants, the identity, sums, products, rational affine substitutions $s\mapsto e(cs+d)$, flat functions $p(1/s)\psi(s)$ and $R$) compiles, for given $(j,a,b)$, to a circuit with value $e(az_j+b)$; an affine substitution is absorbed by replacing $(a,b)$ with $(ca,\,cb+d)$. A box expression (rational constants, terms $e[z_j]$ applying a jet expression to one coordinate, sums and products) compiles to a circuit by compiling each term $e[z_j]$ with $(a,b)=(1,0)$.
--
--   Circuits are a finitary, machine-readable form of the explicit formulas that describe the forcing field. Because they are literally codes of partial recursive functions, the operations above (derivatives, bounds, ball approximations) are amenable to proofs that they are primitive recursive, while the value of a circuit is a concrete real function whose every mixed derivative is again a circuit. This is the mechanism through which the effectivity of the forcing and the computability of its derivative bounds are obtained.
--
--   **Formalization Note** `Atom` is `Fin 4 × ℚ × ℚ × ℕ` and `Circuit` is `Nat.Partrec.Code`; `Code.pair` is addition, `Code.comp` is multiplication, `Code.prec c _` is the atom `data c` and `Code.rfind' c` is the constant `data c`, where `data c` decodes `encode c` (a default value if decoding fails); `Circuit.const` and `Circuit.atom` invert this through `ofNat Code (encode _)` (lemma `data_ofNat_encode`). The real semantics, ball semantics and bounds are `Atom.eval`/`Circuit.eval`, `Atom.approx`/`Circuit.approx` and `Atom.bound`/`Circuit.bound`; the magnitude bound is designed for points with $|z_j|\le\rho$. In `atomDiff` the derivative of $F_{k-2}$ uses atoms of kinds $k+2$ and $k+1$ (i.e. $F_k$ and $F_{k-1}$), and that of $R$ uses kind $4$ (i.e. $F_2$), via `withKind` and `reflect`. The remaining members are evaluation lemmas (`eval_const`, `eval_atom`, `eval_sub`, `eval_add`, `eval_mul`, `eval_suml`, `eval_sum`, `coordinate_ofRational`, `flatten_ofRational`), `flatMono`, `profileDerivative`, `Circuit.polynomial`, `JetExpr.compile` and `BoxExpr.compile`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Circuits.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Circuits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing

namespace OAI

/-! SheetFlows circuits. -/

section
open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal

noncomputable def flatMono (n : ℕ) : ℝ → ℝ := flatJet (Polynomial.X^n)

abbrev Atom := Fin 4 × ℚ × ℚ × ℕ

namespace Atom

def argument (a : Atom) (q : Fin 4 → ℚ) : ℚ := a.2.1*q a.1+a.2.2.1

noncomputable def profile (k : ℕ) : ℝ → ℝ :=
  if k=0 then id else if k=1 then transitionReciprocal else flatMono (k-2)

noncomputable def eval (a : Atom) (z : SpaceTime) : ℝ :=
  profile a.2.2.2 ((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1)

def approx (a : Atom) (q : Fin 4 → ℚ) (n : ℕ) : QBall :=
  if a.2.2.2=0 then QBall.point (argument a q)
  else if a.2.2.2=1 then QBall.reciprocalApprox (argument a q) n
  else QBall.flatApprox (a.2.2.2-2) (argument a q) n

def bound (a : Atom) (R : ℚ) : ℚ :=
  if a.2.2.2=0 then |a.2.1| * |R| + |a.2.2.1|
  else if a.2.2.2=1 then 16 else ((a.2.2.2-2).factorial:ℚ)

end Atom

abbrev Circuit := Nat.Partrec.Code

namespace Circuit

open Nat.Partrec

def data {α : Type*} [Primcodable α] [Inhabited α] (c : Code) : α :=
  (decode (encode c)).getD default

def const (q : ℚ) : Circuit := Code.rfind' (ofNat Code (encode q))
def atom (a : Atom) : Circuit := Code.prec (ofNat Code (encode a)) Code.zero
abbrev add := Code.pair
abbrev mul := Code.comp

def sub (a b : Circuit) : Circuit := add a (mul (const (-1)) b)

noncomputable def eval : Circuit → SpaceTime → ℝ
  | .zero | .succ | .left | .right => fun _ => 0
  | .pair f g => fun z => eval f z + eval g z
  | .comp f g => fun z => eval f z * eval g z
  | .prec a _ => Atom.eval (data a) 
  | .rfind' a => fun _ => (data a : ℚ)

def approx : Circuit → (Fin 4 → ℚ) → ℕ → QBall
  | .zero | .succ | .left | .right => fun _ _ => QBall.point 0
  | .pair f g => fun q n => QBall.add (approx f q n) (approx g q n)
  | .comp f g => fun q n => QBall.mul (approx f q n) (approx g q n)
  | .prec a _ => Atom.approx (data a)
  | .rfind' a => fun _ _ => QBall.point (data a : ℚ)

def bound : Circuit → ℚ → ℚ
  | .zero | .succ | .left | .right => fun _ => 0
  | .pair f g => fun R => bound f R + bound g R
  | .comp f g => fun R => bound f R * bound g R
  | .prec a _ => Atom.bound (data a)
  | .rfind' a => fun _ => |(data a:ℚ)|

@[simp] theorem data_ofNat_encode {α : Type*} [Primcodable α] [Inhabited α] (a : α) :
    data (ofNat Code (encode a)) = a := by
  simp [data]

@[simp] theorem eval_const (q : ℚ) (z : SpaceTime) : eval (const q) z = q := by
  exact congrArg (fun q : ℚ => (q:ℝ)) (data_ofNat_encode q)
@[simp] theorem eval_atom (a : Atom) (z : SpaceTime) : eval (atom a) z = Atom.eval a z := by
  exact congrArg (fun a => Atom.eval a z) (data_ofNat_encode a)
@[simp] theorem eval_sub (a b : Circuit) (z : SpaceTime) :
    eval (sub a b) z = eval a z - eval b z := by simp [sub,add,mul,eval,sub_eq_add_neg]

def ofRational (q : Fin 4 → ℚ) : SpaceTime :=
  (q 0, ![(q 1:ℝ),q 2,q 3])

@[simp] theorem coordinate_ofRational (q : Fin 4 → ℚ) (j : Fin 4) :
    coordinateLinear j (ofRational q) = (q j:ℝ) := by fin_cases j <;> rfl

@[simp] theorem flatten_ofRational (q : Fin 4 → ℚ) (j : Fin 4) :
    flatten (ofRational q) j = (q j:ℝ) := by fin_cases j <;> rfl

end Circuit
end Solenoidal
end

open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace Atom

noncomputable def profileDerivative (k : ℕ) (x : ℝ) : ℝ :=
  if k=0 then 1 else if k=1 then
    -(transitionReciprocal x * transitionReciprocal x) * (flatMono 2 x-flatMono 2 (1-x))
  else flatMono (k-2+2) x - (k-2:ℕ)*flatMono (k-2+1) x

def withKind (a : Atom) (k : ℕ) : Atom := (a.1,a.2.1,a.2.2.1,k)
def reflect (a : Atom) : Atom := (a.1,-a.2.1,1-a.2.2.1,a.2.2.2)

end Atom
namespace Circuit
open Nat.Partrec

def atomDiff (j : Fin 4) (a : Atom) : Circuit :=
  if a.1=j then mul (const a.2.1)
    (if a.2.2.2=0 then const 1 else if a.2.2.2=1 then
      mul (const (-1)) (mul (mul (atom a) (atom a))
        (sub (atom (a.withKind 4)) (atom (a.reflect.withKind 4))))
    else sub (atom (a.withKind (a.2.2.2-2+4)))
      (mul (const (a.2.2.2-2:ℕ)) (atom (a.withKind (a.2.2.2-2+3)))))
  else const 0

@[simp] theorem eval_add (a b : Circuit) (z : SpaceTime) :
    eval (add a b) z = eval a z + eval b z := rfl
@[simp] theorem eval_mul (a b : Circuit) (z : SpaceTime) :
    eval (mul a b) z = eval a z * eval b z := rfl

def diff (j : Fin 4) : Circuit → Circuit
  | .zero | .succ | .left | .right => const 0
  | .pair a b => add (diff j a) (diff j b)
  | .comp a b => add (mul (diff j a) b) (mul a (diff j b))
  | .prec a _ => atomDiff j (data a)
  | .rfind' _ => const 0

def mixed (e : Circuit) : List (Fin 4) → Circuit
  | [] => e
  | j::α => diff j (mixed e α)

noncomputable def field (e : Fin 3 → Circuit) : Field := fun t x j => eval (e j) (t,x)

def suml : List Circuit → Circuit
  | [] => const 0
  | e::l => add e (suml l)

@[simp] theorem eval_suml (l : List Circuit) (z : SpaceTime) :
    eval (suml l) z = (l.map (fun e => eval e z)).sum := by
  induction l with
  | nil => simp [suml]
  | cons e l ih => simp [suml,ih]

noncomputable def sum {ι : Type*} [Fintype ι] (f : ι → Circuit) : Circuit :=
  suml (Finset.univ.toList.map f)

@[simp] theorem eval_sum {ι : Type*} [Fintype ι] (f : ι → Circuit) (z : SpaceTime) :
    eval (sum f) z = ∑ i, eval (f i) z := by simp [sum]

noncomputable def polynomial (p : ℚ[X]) (j : Fin 4) (a b : ℚ) : Circuit :=
  suml (p.support.toList.map (fun n => mul (const (p.coeff n)) (atom (j,a,b,n+2))))

end Circuit
namespace JetExpr

noncomputable def compile : JetExpr → Fin 4 → ℚ → ℚ → Circuit
  | .const q, _, _, _ => Circuit.const q
  | .id, j, a, b => Circuit.atom (j,a,b,0)
  | .add f g, j, a, b => Circuit.add (f.compile j a b) (g.compile j a b)
  | .mul f g, j, a, b => Circuit.mul (f.compile j a b) (g.compile j a b)
  | .affine c d f, j, a, b => f.compile j (c*a) (c*b+d)
  | .flat p, j, a, b => Circuit.polynomial p j a b
  | .reciprocal, j, a, b => Circuit.atom (j,a,b,1)

end JetExpr
namespace BoxExpr

noncomputable def compile : BoxExpr → Circuit
  | .const q => Circuit.const q
  | .coord j e => e.compile j 1 0
  | .add e f => Circuit.add e.compile f.compile
  | .mul e f => Circuit.mul e.compile f.compile

end BoxExpr
end Solenoidal

end OAI


