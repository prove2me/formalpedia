-- Prove2me | Definitions.Def_palomar_zf207_calc
-- name    : palomar_zf207_calc
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-26T23:14:04.283914+00:00
-- url     : https://prove2.me/theorems/ab6b929d-97ad-4db1-b885-aa12c582a6f4
-- title:
--   ZF207: numeric Hilbert-style set-theoretic calculus $\mathcal{C}$
-- statement:
--   Defines the numeric Hilbert-style set-theoretic calculus $\mathcal{C}$ enumerated by the 207-state Turing machine.
--
--   Using the Cantor pairing function $\langle a, b \rangle = \frac{(a+b)(a+b+1)}{2} + b$, natural numbers encode formulas of first-order set theory with variable labels $x_i$ ($i \in \mathbb{N}$): $0$ denotes $\top$, $1$ denotes $\bot$ (as $x_0 \in x_0$), $I(a,b) = 4\langle a,b\rangle$ encodes $a \to b$, $M(a,b) = 4\langle a,b\rangle + 1$ encodes $x_a \in x_b$, $U(a,B) = 4\langle B,a\rangle + 2$ encodes $\forall x_a\, B$, and $E(a,b) = 4\langle a,b\rangle + 3$ encodes $x_a = x_b$, with negation $N(B) = I(B,1)$.
--
--   The inductive predicate $\mathrm{ProvC}(n)$ captures derivability in $\mathcal{C}$ from the constant $\top$ (code $0$), the propositional axiom $\rho_8$, the six quantifier/equality heads `head1`--`head6`, and the definable pointed-hull gate schema `gateF` (guarded by $c \neq a, b$), closed under modus ponens and universal generalization.
--
--   This calculus bridges the physical 207-state Turing machine (which halts only upon deriving code $1$ in $\mathcal{C}$) and semantic soundness in models of $\mathrm{ZF}$.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Section 3 (The calculus C, pp. 3-4)

namespace PalomarZF207Calc

def cantor (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

def Ic (a b : Nat) : Nat := 4 * cantor a b
def Mc (a b : Nat) : Nat := 4 * cantor a b + 1
def Uc (a B : Nat) : Nat := 4 * cantor B a + 2
def Ec (a b : Nat) : Nat := 4 * cantor a b + 3
def Nc (B : Nat) : Nat := Ic B 1

def rho8 (a b c u : Nat) : Nat :=
  Ic (Ic (Ic c u) a) (Ic (Ic a c) (Ic b c))

def head1 (x y : Nat) : Nat := Ic (Nc (Uc y (Nc (Uc y x)))) x
def head2 (x y z : Nat) : Nat := Ic (Uc y (Uc z x)) (Uc z (Uc y x))
def head3 (x y z : Nat) : Nat := Ic (Mc x y) (Ic (Ec x z) (Mc z y))
def head4 (x y z : Nat) : Nat := Ic (Ec x y) (Ic (Mc z x) (Mc z y))
def head5 (x y : Nat) : Nat := Nc (Uc y (Nc (Ec x y)))
def head6 (x y z : Nat) : Nat := Ic (Uc y z) (Ic (Uc y (Ic z x)) (Uc y x))

def gateG (a b c : Nat) : Nat :=
  let subBA := Uc c (Ic (Mc c b) (Mc c a))
  let stepEx := Nc (Uc a (Ic c (Nc (Mc a c))))
  let stepAll := Uc a (Ic c stepEx)
  let hullBody := Nc (Uc b (Ic c (Nc (Uc b (Ic subBA stepAll)))))
  let lhs := Uc a (Ic (Mc a c) hullBody)
  let rhs := Nc (Ic c (Mc a c))
  Ic lhs rhs

def gateF (a b c : Nat) : Nat :=
  let delta := Ic (Ec a b) (Uc c (Ec a b))
  let vax := Ic (Mc a b) (Uc c (Mc a b))
  let q := Uc c (gateG a b c)
  Nc (Ic delta (Ic vax q))

inductive ProvC : Nat → Prop where
  | truth : ProvC 0
  | mp {a b : Nat} : ProvC (Ic a b) → ProvC a → ProvC b
  | gen (a : Nat) {B : Nat} : ProvC B → ProvC (Uc a B)
  | ax_rho8 (a b c u : Nat) : ProvC (rho8 a b c u)
  | ax_h1 (x y : Nat) : ProvC (head1 x y)
  | ax_h2 (x y z : Nat) : ProvC (head2 x y z)
  | ax_h3 (x y z : Nat) : ProvC (head3 x y z)
  | ax_h4 (x y z : Nat) : ProvC (head4 x y z)
  | ax_h5 (x y : Nat) : ProvC (head5 x y)
  | ax_h6 (x y z : Nat) : ProvC (head6 x y z)
  | ax_gate (a b c : Nat) : c ≠ a → c ≠ b → ProvC (gateF a b c)

end PalomarZF207Calc


