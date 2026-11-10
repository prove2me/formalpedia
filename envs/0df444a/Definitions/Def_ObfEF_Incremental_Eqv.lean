-- Prove2me | Definitions.Def_ObfEF_Incremental_Eqv
-- name    : ObfEF_Incremental_Eqv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:05.574472+00:00
-- url     : https://prove2.me/theorems/6c4ebf80-44fe-484f-bbe5-9108f469cb10
-- title:
--   Equivalence formulas Eqv_{C0,C1} of two circuits (Definition 2.7)
-- statement:
--   Let $C$ be a circuit over $B$ with $il$ inputs and outputs $u_1,\dots,u_{ol}$, and let $k\in[ol]$. The **straight-line program** $C^{(k)}=(g_1,\dots,g_t)$ consists of the vertices of $C$ from which $u_k$ is reachable, in the canonical topological order of $C$, so that $g_t=u_k$. The instruction $t_i$ of $g_i$ is the input variable $x_r$ if $g_i$ is the input $v_r$, the constant $c$ for a constant vertex, and $\neg g_{i'}$, $g_{i'}\wedge g_{i''}$ or $g_{i'}\vee g_{i''}$ for a gate with inputs $g_{i'},g_{i''}$.
--
--   For programs $A=(g_1,\dots,g_t)$ and $A'=(g'_1,\dots,g'_{t'})$ and distinct variables $y_1,\dots,y_t,z_1,\dots,z_{t'}$ outside $x=(x_1,\dots,x_{il})$, $\mathrm{Def}_A(x,y)$ is the conjunction of $\mathrm{eq}(y_i,t_i)$ over $i\in[t]$, with $y_{i'}$ in place of $g_{i'}$ in $t_i$, and $\mathrm{Def}_{A'}(x,z)$ is defined in the same way. Then
--   $$\mathrm{Eq}_{A,A'}=\big(\mathrm{Def}_A(x,y)\wedge\mathrm{Def}_{A'}(x,z)\big)\to\mathrm{eq}(y_t,z_{t'}),\qquad \mathrm{Eqv}_{C_0,C_1}=\bigwedge_{k\in[ol]}\mathrm{Eq}_{C_0^{(k)},C_1^{(k)}},$$
--   where distinct conjuncts use disjoint sets of variables outside $x$. Everything is written over $\{\to,\bot\}$ by the abbreviations of p. 27. $\mathrm{Eqv}_{C_0,C_1}$ is a tautology if and only if $C_0\equiv C_1$.
--
--   **Formalization Note.** The canonical topological order lists the inputs $v_1,\dots,v_{il}$ and then the noninput vertices in their numbering. The variable of vertex $v$ in conjunct $k$ on side $b\in\{0,1\}$ is $x_{il+\langle k,\,2\,\mathrm{idx}(v)+b\rangle}$ with $\langle\cdot,\cdot\rangle$ = `Nat.pair`, $\mathrm{idx}(v_r)=r$ and $\mathrm{idx}(j)=il+j$; this makes all auxiliary variables distinct and different from $x_0,\dots,x_{il-1}$ (renaming variables changes neither provability nor proof size). Conjunctions are right-nested in program order and in output order.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 28, Definition 2.7

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula

/-!
# Equivalence formulas `Eqv_{C₀,C₁}` (Definition 2.7)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 28,
Definition 2.7 (after [Kra26]).

Conventions.
* The canonical topological order of a circuit `C : Circuit (Fin il) ol` lists the input vertices
  `v₁, …, v_il` and then the noninput vertices `0, …, |C| - 1` in their numbering.
* The straight-line program `C^(k)` is the sublist of the vertices from which `u_k` is reachable;
  its last entry is `u_k`.
* Input variables: `x_r = var r` (`r < il`). The auxiliary variable of vertex `v` in the program of
  output `k` of circuit `b ∈ {0, 1}` is `var (il + pair(k, 2·idx(v) + b))`, with `idx(v_r) = r` and
  `idx(j) = il + j`: distinct across positions, across the two circuits and across conjuncts, and
  outside `x`.
* `Def_A` and `Eqv` are right-nested conjunctions in program order and in output order; all
  connectives are the abbreviations of p. 27 (`Fml.conj`, `Fml.disj`, `Fml.neg`, `Fml.eqF`).
-/

namespace ObfEF.Incremental

open Fml Classical

namespace Circuit

variable {il ol : ℕ}

/-- `idx(v)`: the position of a vertex in the canonical order (inputs first). -/
def vidx (C : Circuit (Fin il) ol) : Fin il ⊕ Fin C.size → ℕ
  | .inl r => r
  | .inr j => il + j

/-- The vertices of `C` in its canonical topological order. -/
def canonicalOrder (C : Circuit (Fin il) ol) : List (Fin il ⊕ Fin C.size) :=
  (List.finRange il).map Sum.inl ++ (List.finRange C.size).map Sum.inr

/-- The straight-line program `C^(k)`: the vertices from which `u_k` is reachable, in canonical
topological order. -/
noncomputable def program (C : Circuit (Fin il) ol) (k : Fin ol) : List (Fin il ⊕ Fin C.size) :=
  C.canonicalOrder.filter fun v => decide (C.Reaches v (C.out k))

/-- The auxiliary variable `y` (`b = false`) or `z` (`b = true`) of vertex `v` in conjunct `k`. -/
def auxVar (C : Circuit (Fin il) ol) (k : Fin ol) (b : Bool) (v : Fin il ⊕ Fin C.size) : Fml :=
  var (il + Nat.pair k (2 * C.vidx v + if b then 1 else 0))

/-- The instruction `t_i` of a vertex, with the auxiliary variables of its operands in place of
the operands: `x_r` for the input `v_r`, the constant, `¬a`, `a ∧ b`, `a ∨ b`. -/
def instrF (C : Circuit (Fin il) ol) (y : Fin il ⊕ Fin C.size → Fml) :
    Fin il ⊕ Fin C.size → Fml
  | .inl r => var r
  | .inr j =>
      match C.op j with
      | .const c => ofBool c
      | .not a => neg (y (C.liftArg j a))
      | .and a b => conj (y (C.liftArg j a)) (y (C.liftArg j b))
      | .or a b => disj (y (C.liftArg j a)) (y (C.liftArg j b))

/-- `Def_A(x, y) = ⋀_i eq(y_i, t_i)` for `A = C^(k)` with the variables of side `b`. -/
noncomputable def defF (C : Circuit (Fin il) ol) (k : Fin ol) (b : Bool) : Fml :=
  bigConj ((C.program k).map fun v => eqF (C.auxVar k b v) (C.instrF (C.auxVar k b) v))

end Circuit

/-- `Eq_{C₀^(k), C₁^(k)} = (Def_A(x, y) ∧ Def_{A'}(x, z)) → eq(y_t, z_{t'})`. -/
noncomputable def eqOutput {il ol : ℕ} (C₀ C₁ : Circuit (Fin il) ol) (k : Fin ol) : Fml :=
  imp (conj (C₀.defF k false) (C₁.defF k true))
    (eqF (C₀.auxVar k false (C₀.out k)) (C₁.auxVar k true (C₁.out k)))

/-- The equivalence formula `Eqv_{C₀,C₁} = ⋀_{k ∈ [ol]} Eq_{C₀^(k), C₁^(k)}`. -/
noncomputable def Eqv {il ol : ℕ} (C₀ C₁ : Circuit (Fin il) ol) : Fml :=
  bigConj ((List.finRange ol).map (eqOutput C₀ C₁))

end ObfEF.Incremental


