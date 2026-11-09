-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
-- name    : TreeEquivalenceHORS_Equivalence_Compiler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:05.138416+00:00
-- url     : https://prove2.me/theorems/4852827f-d017-412f-a32a-f575f5df323e
-- title:
--   The intermediate compiler $M\mapsto G^{\diamond}_M$ over $\Sigma_0$ (Figure 3), Church realizability, $\mathrm{Pol}_m$, $\mathrm{Reg}_m$ and the output maps $T^{\diamond}$
-- statement:
--   Let $C=o\to o$, $N=C\to C$, $P=N\to N\to N$ (orders $1,2,3$).
--
--   1. **Arithmetic library** (Section 5.1, Equation (17)): $\mathrm{Zero}\,f\,x\to x$, $\mathrm{One}\,f\,x\to f\,x$, $\mathrm{Succ}\,n\,f\,x\to f\,(n\,f\,x)$, $\mathrm{Add}\,m\,n\,f\,x\to m\,f\,(n\,f\,x)$, $\mathrm{Mul}\,m\,n\,f\,x\to m\,(n\,f)\,x$, $\mathrm{Pos}\,u\,v\,r\,s\,f\,x\to\mathrm{Add}\,(\mathrm{Mul}\,u\,r)\,(\mathrm{Mul}\,v\,s)\,f\,x$, $\mathrm{Neg}\,u\,v\,r\,s\,f\,x\to\mathrm{Add}\,(\mathrm{Mul}\,u\,s)\,(\mathrm{Mul}\,v\,r)\,f\,x$, $\mathrm{Seed}_\pm\,u\,v\,f\,x\to\mathrm{One}/\mathrm{Zero}\,f\,x$, and $\mathrm{Next}_\pm\,p\,q\,u\,v\,f\,x\to\mathrm{Pos}/\mathrm{Neg}\,u\,(\mathrm{Succ}\,v)\,(p\,u\,(\mathrm{Succ}\,v))\,(q\,u\,(\mathrm{Succ}\,v))\,f\,x$.
--   2. **Control rules** (Figure 3). For each $i\in I_M$, $F_i:P\to P\to N^6\to o$ with parameters $p,q,u,v,r,s,h,k$ emits $b\,z\,c_1\,c_2$; both continuations receive $p'=\mathrm{Next}_+\,p\,q$, $q'=\mathrm{Next}_-\,p\,q$. An increment applies $\mathrm{Succ}$ to the positive coordinate of its counter and duplicates the call to $F_{\widehat{i+1}}$. A test $\mathrm{dec}\,A(j)$ continues with $F_{\widehat{i+1}}\,p'\,q'\,u\,v\,r\,s\,(\mathrm{Pos}\,h\,k\,(p\,u\,v)\,(q\,u\,v))\,(\mathrm{Neg}\,h\,k\,(p\,u\,v)\,(q\,u\,v))$ and $F_{\hat j}\,p'\,q'\,u\,(\mathrm{Succ}\,v)\,r\,s\,(\mathrm{Pos}\,h\,k\,u\,v)\,(\mathrm{Neg}\,h\,k\,u\,v)$; $\mathrm{dec}\,B(j)$ is the same on $r,s$. Here $\hat j=j$ for $j\in I_M$ and $0$ otherwise. The halt rule is $F_0\,\vec t\to b\,(w^\diamond\,a\,z)\,K\,K$ with $w^L=h$, $w^R=k$; $K\to b\,z\,K\,K$; $S\to F_{\hat1}\,\mathrm{Seed}_+\,\mathrm{Seed}_-\,\mathrm{Zero}\,\mathrm{Zero}\,\mathrm{Zero}\,\mathrm{Zero}\,\mathrm{One}\,\mathrm{Zero}$. $G^\diamond_M$ is the scheme over $\Sigma_0$ with these rules.
--   3. **Realizability** (Equation (18)). $V_o$ is the set of all partial maps $\mathbb N^*\rightharpoonup\Sigma_0$ and $V_{\sigma\to\tau}=V_\tau^{V_\sigma}$. For closed $t$: $t\Vdash_oT$ iff $\mathrm{Obs}_G(t,w,a)\leftrightarrow T(w)=a$ for all $w,a$; $t\Vdash_{\sigma\to\tau}F$ iff $u\Vdash_\sigma U$ implies $t\,u\Vdash_\tau F(U)$ for all closed $u:\sigma$. $\mathrm{Num}(t,n)$ means $t\Vdash_N(f,X)\mapsto f^n(X)$.
--   4. **Pairs and polynomials.** $(u,v)\otimes(r,s)=(ur+vs,us+vr)$, $\mathrm{inc}(u,v)=(u+1,v)$, $\mathrm{dec}(u,v)=(u,v+1)$, $C_0(u,v)=(1,0)$, $C_{m+1}(u,v)=(u,v+1)\otimes C_m(u,v+1)$ (Equation (14)). $\mathrm{Pol}_m(p,q)$ (Equation (19)) asserts $\mathrm{Num}(p\,t\,s,P^+_m(u,v))$ and $\mathrm{Num}(q\,t\,s,P^-_m(u,v))$ for all $u,v\in\mathbb N$ and all closed $t,s$ with $\mathrm{Num}(t,u)$, $\mathrm{Num}(s,v)$. $\mathrm{Reg}_m(\vec t;A,B,W)$ (Equation (20)) is $\mathrm{Pol}_m(p,q)$ plus $\mathrm{Num}$ for the six components. The pair update (21) applies $\mathrm{inc}$ to the selected counter at an increment, multiplies $W$ by $C_m$ of the old counter at a zero guess, and applies $\mathrm{dec}$ and multiplies $W$ by the old counter at a positive guess.
--   5. **Output maps** (Equations (23)–(24)). $T^\diamond(m,i,R)$ is $b\,(a^{W^\diamond}z)\,K\,K$ for $i\notin I_M$ and $b\,z\,T^\diamond(m+1,i_1,R_1)\,T^\diamond(m+1,i_2,R_2)$ for $i\in I_M$, evaluated address by address; $W^L,W^R$ are the first and second weight components.
--
--   **Formalization Note** Nonterminal indices: $0$ Zero, $1$ One, $2$ Succ, $3$ Add, $4$ Mul, $5$ Pos, $6$ Neg, $7$ Seed$_+$, $8$ Seed$_-$, $9$ Next$_+$, $10$ Next$_-$, $11$ $S$, $12$ $K$, $13+i$ for $F_i$ ($0\le i\le L$). `contArgs`, `pairStep`, `nextPos` give the argument tuple, natural pairs and position of each continuation; `argsAlong`, `pairsAlong` follow them along a candidate word from the start rule. `Num` and `Pol` include that their terms are closed and of type $N$, resp. $P$.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Sections 5.1–5.5, Figure 3 (printed p. 15 / PDF p. 17), Equations (14), (17)–(21), (23)–(24), printed pp. 13–19 / PDF pp. 15–21

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines

namespace TreeEquivalenceHORS.Equivalence

/-! # The intermediate compiler `M ↦ G^⋄_M` over `Σ₀` (Section 5.1–5.2, Figure 3; PDF pp. 15–17)

Nonterminal indices in every compiled scheme:
`0 Zero, 1 One, 2 Succ, 3 Add, 4 Mul, 5 Pos, 6 Neg, 7 Seed₊, 8 Seed₋, 9 Next₊, 10 Next₋, 11 S,
12 K`, and `13 + i` for the control nonterminal `Fᵢ`, `0 ≤ i ≤ L`.
Terminals of `Σ₀`: `0 = z`, `1 = a`, `2 = b`. Rule parameters are positional (`var i`). -/

open Tm

/-- `C = o → o`. -/
def tyC : Ty := .arr .o .o
/-- `N = C → C`. -/
def tyN : Ty := .arr tyC tyC
/-- `P = N → N → N`. -/
def tyP : Ty := .arr tyN (.arr tyN tyN)
/-- The control type `P → P → N⁶ → o`. -/
def tyF : Ty := Ty.ofArgs [tyP, tyP, tyN, tyN, tyN, tyN, tyN, tyN]

/-- Nonterminal indices. -/
def iZero : ℕ := 0
def iOne : ℕ := 1
def iSucc : ℕ := 2
def iAdd : ℕ := 3
def iMul : ℕ := 4
def iPos : ℕ := 5
def iNeg : ℕ := 6
def iSeedP : ℕ := 7
def iSeedM : ℕ := 8
def iNextP : ℕ := 9
def iNextM : ℕ := 10
def iS : ℕ := 11
def iK : ℕ := 12
/-- The index of the control nonterminal `Fᵢ`. -/
def iF (i : ℕ) : ℕ := 13 + i

/-- Terminals of `Σ₀`. -/
def tz : Tm := .tm 0
def ta : Tm := .tm 1
def tb : Tm := .tm 2

/-- Types of the eleven arithmetic nonterminals (Lemma 5.1's type audit). -/
def arithTys : List Ty :=
  [tyN, tyN, .arr tyN tyN, .arr tyN (.arr tyN tyN), .arr tyN (.arr tyN tyN),
   .arr tyN (.arr tyN (.arr tyN (.arr tyN tyN))), .arr tyN (.arr tyN (.arr tyN (.arr tyN tyN))),
   tyP, tyP, .arr tyP (.arr tyP tyP), .arr tyP (.arr tyP tyP)]

/-- The arithmetic rules of Section 5.1 and Equation (17), in parameter order:
* `Zero f x → x`, `One f x → f x`, `Succ n f x → f (n f x)`,
* `Add m n f x → m f (n f x)`, `Mul m n f x → m (n f) x`,
* `Pos u v r s f x → Add (Mul u r) (Mul v s) f x`, `Neg u v r s f x → Add (Mul u s) (Mul v r) f x`,
* `Seed₊ u v f x → One f x`, `Seed₋ u v f x → Zero f x`,
* `Next₊ p q u v f x → Pos u (Succ v) (p u (Succ v)) (q u (Succ v)) f x`, and `Next₋` with `Neg`. -/
def arithRules : List Tm :=
  [ var 1,
    app (var 0) (var 1),
    app (var 1) (apps (var 0) [var 1, var 2]),
    apps (var 0) [var 2, apps (var 1) [var 2, var 3]],
    apps (var 0) [app (var 1) (var 2), var 3],
    apps (nt iAdd) [apps (nt iMul) [var 0, var 2], apps (nt iMul) [var 1, var 3], var 4, var 5],
    apps (nt iAdd) [apps (nt iMul) [var 0, var 3], apps (nt iMul) [var 1, var 2], var 4, var 5],
    apps (nt iOne) [var 2, var 3],
    apps (nt iZero) [var 2, var 3],
    apps (nt iPos) [var 2, app (nt iSucc) (var 3), apps (var 0) [var 2, app (nt iSucc) (var 3)],
      apps (var 1) [var 2, app (nt iSucc) (var 3)], var 4, var 5],
    apps (nt iNeg) [var 2, app (nt iSucc) (var 3), apps (var 0) [var 2, app (nt iSucc) (var 3)],
      apps (var 1) [var 2, app (nt iSucc) (var 3)], var 4, var 5] ]

/-- The two sides `⋄ ∈ {L, R}` of the compiler. -/
inductive Side : Type where
  | L : Side
  | R : Side
  deriving DecidableEq, Repr

namespace Machine

/-- Normalization `ĵ = j` for `j ∈ I_M` and `ĵ = 0` otherwise. -/
def norm (M : Machine) (j : ℕ) : ℕ := if M.Active j then j else 0

end Machine

/-- The control call `F_ĵ a₁ ⋯ a₈`. -/
def callF (M : Machine) (j : ℕ) (as : List Tm) : Tm := apps (nt (iF (M.norm j))) as

/-- The rule body of `Fᵢ` (Figure 3), parameters `p q u v r s h k = var 0, …, var 7`, with
`p' = Next₊ p q`, `q' = Next₋ p q`:
* `inc A`: `b z (F_{î+1} p' q' (Succ u) v r s h k) (same)`;
* `inc B`: `b z (F_{î+1} p' q' u v (Succ r) s h k) (same)`;
* `dec A (j)`: `b z (F_{î+1} p' q' u v r s (Pos h k (p u v) (q u v)) (Neg h k (p u v) (q u v)))
  (F_ĵ p' q' u (Succ v) r s (Pos h k u v) (Neg h k u v))`;
* `dec B (j)`: the same with `r, s` in place of `u, v`;
* halt (`i ∉ I_M`, used for `F₀`): `b (w⋄ a z) K K` with `w_L = h`, `w_R = k`. -/
def ctrlBody (side : Side) (M : Machine) (i : ℕ) : Tm :=
  let p' := apps (nt iNextP) [var 0, var 1]
  let q' := apps (nt iNextM) [var 0, var 1]
  let sc := fun t => app (nt iSucc) t
  match M.lookup i with
  | some .incA =>
      let c := callF M (i + 1) [p', q', sc (var 2), var 3, var 4, var 5, var 6, var 7]
      apps tb [tz, c, c]
  | some .incB =>
      let c := callF M (i + 1) [p', q', var 2, var 3, sc (var 4), var 5, var 6, var 7]
      apps tb [tz, c, c]
  | some (.decA j) =>
      apps tb [tz,
        callF M (i + 1) [p', q', var 2, var 3, var 4, var 5,
          apps (nt iPos) [var 6, var 7, apps (var 0) [var 2, var 3], apps (var 1) [var 2, var 3]],
          apps (nt iNeg) [var 6, var 7, apps (var 0) [var 2, var 3], apps (var 1) [var 2, var 3]]],
        callF M j [p', q', var 2, sc (var 3), var 4, var 5,
          apps (nt iPos) [var 6, var 7, var 2, var 3], apps (nt iNeg) [var 6, var 7, var 2, var 3]]]
  | some (.decB j) =>
      apps tb [tz,
        callF M (i + 1) [p', q', var 2, var 3, var 4, var 5,
          apps (nt iPos) [var 6, var 7, apps (var 0) [var 4, var 5], apps (var 1) [var 4, var 5]],
          apps (nt iNeg) [var 6, var 7, apps (var 0) [var 4, var 5], apps (var 1) [var 4, var 5]]],
        callF M j [p', q', var 2, var 3, var 4, sc (var 5),
          apps (nt iPos) [var 6, var 7, var 4, var 5], apps (nt iNeg) [var 6, var 7, var 4, var 5]]]
  | none =>
      apps tb [apps (match side with | .L => var 6 | .R => var 7) [ta, tz], nt iK, nt iK]

/-- The start rule `S → F_{1̂} Seed₊ Seed₋ Zero Zero Zero Zero One Zero`. -/
def startBody (M : Machine) : Tm :=
  callF M 1 [nt iSeedP, nt iSeedM, nt iZero, nt iZero, nt iZero, nt iZero, nt iOne, nt iZero]

/-- The padding rule `K → b z K K`. -/
def kBody : Tm := apps tb [tz, nt iK, nt iK]

/-- The compiled intermediate scheme `G^⋄_M = ⟦M⟧^⋄` over `Σ₀` (Figure 3): the arithmetic library,
`S`, `K`, and the control nonterminals `F₀, …, F_L`. -/
def compile (side : Side) (M : Machine) : HORS where
  alphabet := sigma0
  nts := arithTys ++ [Ty.o, Ty.o] ++ List.replicate (M.length + 1) tyF
  rules := arithRules ++ [startBody M, kBody] ++ (List.range (M.length + 1)).map (ctrlBody side M)
  start := iS

/-! ## The realization relation (Section 5.4, Equation (18)) -/

/-- The semantic domains `V_σ`: `V_o` is the set of all partial observation maps `ℕ* ⇀ Σ₀`
(`none` is `†`), and `V_{σ→τ}` is the set of all functions `V_σ → V_τ`. -/
def Val : Ty → Type
  | .o => List ℕ → Option (Fin 3)
  | .arr σ τ => Val σ → Val τ

/-- The logical relation `t ⊩_σ v` of Equation (18) for the scheme `G` (over `Σ₀`):
`t ⊩_o T` iff for all `w` and terminals `a`, `Obs_G(t, w, a) ↔ T(w) = a`; and `t ⊩_{σ→τ} F` iff
for every closed term `u : σ` and every `U` with `u ⊩_σ U`, `t u ⊩_τ F(U)`. -/
def Real (G : HORS) : (σ : Ty) → Tm → Val σ → Prop
  | .o, t, T => ∀ (w : List ℕ) (a : Fin 3), G.Obs t w a.val ↔ T w = some a
  | .arr σ τ, t, F => ∀ (u : Tm) (U : Val σ), G.typeOf [] u = some σ → Real G σ u U →
      Real G τ (.app t u) (F U)

/-- The iteration `(f, X) ↦ fⁿ(X)` in `V_N`. -/
def churchVal (n : ℕ) : Val tyN := fun F X => (show Val .o → Val .o from F)^[n] X

/-- `Num(t, n)`: `t` is a closed term of type `N` and `t ⊩_N (λ f X. fⁿ(X))`. -/
def Num (G : HORS) (t : Tm) (n : ℕ) : Prop :=
  G.typeOf [] t = some tyN ∧ Real G tyN t (churchVal n)

/-- The observation map of the one-node tree `z`. -/
def zVal : Val .o := fun w => if w = [] then some 0 else none

/-- The observation map of the chain `aⁿ z` (`n` nodes `a` along child `0`, ending in `z`). -/
def chainVal (n : ℕ) : Val .o := fun w =>
  if w.all (· = 0) then (if w.length < n then some 1 else if w.length = n then some 0 else none)
  else none

/-! ## Signed pairs and the polynomial pair `C_m` (Sections 5.1, Equation (14)) -/

/-- Pair multiplication `(u, v) ⊗ (r, s) = (ur + vs, us + vr)`. -/
def pmul (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
/-- `inc(u, v) = (u + 1, v)`. -/
def pinc (x : ℕ × ℕ) : ℕ × ℕ := (x.1 + 1, x.2)
/-- `dec(u, v) = (u, v + 1)`. -/
def pdec (x : ℕ × ℕ) : ℕ × ℕ := (x.1, x.2 + 1)

/-- `C_m(u, v) = (P⁺_m(u, v), P⁻_m(u, v))`: `C₀(u, v) = (1, 0)`,
`C_{m+1}(u, v) = (u, v + 1) ⊗ C_m(u, v + 1)` (Equation (14)). -/
def Cpoly : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _ => (1, 0)
  | m + 1, u, v => pmul (u, v + 1) (Cpoly m u (v + 1))

/-- `Pol_m(p, q)` (Equation (19)): `p, q` are closed terms of type `P` and, for all `u, v ∈ ℕ`
and all closed `t, s : N` with `Num(t, u)` and `Num(s, v)`,
`Num(p t s, P⁺_m(u, v))` and `Num(q t s, P⁻_m(u, v))`. -/
def Pol (G : HORS) (m : ℕ) (p q : Tm) : Prop :=
  G.typeOf [] p = some tyP ∧ G.typeOf [] q = some tyP ∧
    ∀ (u v : ℕ) (t s : Tm), Num G t u → Num G s v →
      Num G (apps p [t, s]) (Cpoly m u v).1 ∧ Num G (apps q [t, s]) (Cpoly m u v).2

/-- A closed argument tuple `t⃗ = (p, q, u, v, r, s, h, k)` of a state call. -/
structure StateArgs : Type where
  (p q u v r s h k : Tm)

/-- The argument list `[p, q, u, v, r, s, h, k]`. -/
def StateArgs.toList (t : StateArgs) : List Tm := [t.p, t.q, t.u, t.v, t.r, t.s, t.h, t.k]

/-- Natural-pair data `R = (A, B, W) ∈ (ℕ²)³` of a state: counters `A`, `B` and weight `W`. -/
structure PairState : Type where
  (A B W : ℕ × ℕ)

/-- `Reg_m(t⃗; A, B, W)` (Equation (20)): `Pol_m(p, q)` and `Num` for the six pair components. -/
def Reg (G : HORS) (m : ℕ) (t : StateArgs) (R : PairState) : Prop :=
  Pol G m t.p t.q ∧ Num G t.u R.A.1 ∧ Num G t.v R.A.2 ∧ Num G t.r R.B.1 ∧ Num G t.s R.B.2 ∧
    Num G t.h R.W.1 ∧ Num G t.k R.W.2

namespace Machine

/-- The control successor `i_e` of position `i` for choice `e` (first coordinate of `δ_e^M`). -/
def nextPos (M : Machine) (i : ℕ) (e : Choice) : ℕ :=
  match M.lookup i, e with
  | some (.decA j), .two => j
  | some (.decB j), .two => j
  | some _, _ => i + 1
  | none, _ => i

/-- The pair update `R_e` of Equation (21) at clock `m`, position `i` and choice `e`:
increment applies `inc` to the selected counter; a zero guess keeps it and multiplies the weight by
`C_m` of the old counter pair; a positive guess applies `dec` to it and multiplies the weight by
the old counter pair. The other counter is unchanged. -/
def pairStep (M : Machine) (m i : ℕ) (e : Choice) (R : PairState) : PairState :=
  match M.lookup i, e with
  | some .incA, _ => ⟨pinc R.A, R.B, R.W⟩
  | some .incB, _ => ⟨R.A, pinc R.B, R.W⟩
  | some (.decA _), .one => ⟨R.A, R.B, pmul R.W (Cpoly m R.A.1 R.A.2)⟩
  | some (.decA _), .two => ⟨pdec R.A, R.B, pmul R.W R.A⟩
  | some (.decB _), .one => ⟨R.A, R.B, pmul R.W (Cpoly m R.B.1 R.B.2)⟩
  | some (.decB _), .two => ⟨R.A, pdec R.B, pmul R.W R.B⟩
  | none, _ => R

/-- The argument tuple of continuation `e` in the instantiated rule of `Fᵢ` (Figure 3), given the
call's arguments `t⃗`. -/
def contArgs (M : Machine) (i : ℕ) (e : Choice) (t : StateArgs) : StateArgs :=
  let p' := apps (nt iNextP) [t.p, t.q]
  let q' := apps (nt iNextM) [t.p, t.q]
  let sc := fun x => app (nt iSucc) x
  match M.lookup i, e with
  | some .incA, _ => ⟨p', q', sc t.u, t.v, t.r, t.s, t.h, t.k⟩
  | some .incB, _ => ⟨p', q', t.u, t.v, sc t.r, t.s, t.h, t.k⟩
  | some (.decA _), .one => ⟨p', q', t.u, t.v, t.r, t.s,
      apps (nt iPos) [t.h, t.k, apps t.p [t.u, t.v], apps t.q [t.u, t.v]],
      apps (nt iNeg) [t.h, t.k, apps t.p [t.u, t.v], apps t.q [t.u, t.v]]⟩
  | some (.decA _), .two => ⟨p', q', t.u, sc t.v, t.r, t.s,
      apps (nt iPos) [t.h, t.k, t.u, t.v], apps (nt iNeg) [t.h, t.k, t.u, t.v]⟩
  | some (.decB _), .one => ⟨p', q', t.u, t.v, t.r, t.s,
      apps (nt iPos) [t.h, t.k, apps t.p [t.r, t.s], apps t.q [t.r, t.s]],
      apps (nt iNeg) [t.h, t.k, apps t.p [t.r, t.s], apps t.q [t.r, t.s]]⟩
  | some (.decB _), .two => ⟨p', q', t.u, t.v, t.r, sc t.s,
      apps (nt iPos) [t.h, t.k, t.r, t.s], apps (nt iNeg) [t.h, t.k, t.r, t.s]⟩
  | none, _ => t

/-- The initial argument tuple of the start rule: `(Seed₊, Seed₋, Zero, Zero, Zero, Zero, One, Zero)`. -/
def initArgs : StateArgs :=
  ⟨nt iSeedP, nt iSeedM, nt iZero, nt iZero, nt iZero, nt iZero, nt iOne, nt iZero⟩

/-- The initial natural pairs `A = B = (0, 0)`, `W = (1, 0)`. -/
def initPairs : PairState := ⟨(0, 0), (0, 0), (1, 0)⟩

/-- Along a candidate word, from clock `m`, position `i`, arguments `t⃗` and pairs `R`: the final
position, argument tuple and pairs obtained by following the continuations. -/
def along (M : Machine) : ℕ → ℕ → StateArgs → PairState → List Choice → ℕ × StateArgs × PairState
  | _, i, t, R, [] => (i, t, R)
  | m, i, t, R, e :: v =>
      along M (m + 1) (M.nextPos i e) (M.contArgs i e t) (M.pairStep m i e R) v

/-- The argument tuple reached along a candidate prefix `v` from the start rule. -/
def argsAlong (M : Machine) (v : List Choice) : StateArgs := (M.along 0 1 initArgs initPairs v).2.1

/-- The natural pairs reached along a candidate prefix `v`. -/
def pairsAlong (M : Machine) (v : List Choice) : PairState := (M.along 0 1 initArgs initPairs v).2.2

end Machine

/-- The child index of choice `e` in a candidate node `b`: `one ↦ 1`, `two ↦ 2`. -/
def Choice.child : Choice → ℕ
  | .one => 1
  | .two => 2

/-! ## The output observation maps `T^⋄(m, i, R)` (Equations (23)–(24)) -/

/-- The observation map of the padding tree `K = b z K K`. -/
def kVal : List ℕ → Option (Fin 3)
  | [] => some 2
  | c :: w => if c = 0 then zVal w else if c = 1 ∨ c = 2 then kVal w else none

/-- The weight component selected by the side: `W^L = W⁺` (first), `W^R = W⁻` (second). -/
def Side.pick : Side → ℕ × ℕ → ℕ
  | .L, W => W.1
  | .R, W => W.2

/-- `T^⋄(m, i, R)` (Equation (23)) evaluated at a finite address: for `i ∉ I_M` it is
`b (a^{W⋄} z) K K`; for `i ∈ I_M` it is `b z T^⋄(m+1, i₁, R₁) T^⋄(m+1, i₂, R₂)`, with `i_e`, `R_e`
the candidate successor and pair update of Equation (21) for choice `e`. -/
def Tmap (side : Side) (M : Machine) : ℕ → ℕ → PairState → List ℕ → Option (Fin 3)
  | _, _, _, [] => some 2
  | m, i, R, c :: w =>
      if M.Active i then
        (if c = 0 then zVal w
         else if c = 1 then Tmap side M (m + 1) (M.nextPos i .one) (M.pairStep m i .one R) w
         else if c = 2 then Tmap side M (m + 1) (M.nextPos i .two) (M.pairStep m i .two R) w
         else none)
      else
        (if c = 0 then chainVal (side.pick R.W) w
         else if c = 1 ∨ c = 2 then kVal w
         else none)

end TreeEquivalenceHORS.Equivalence


