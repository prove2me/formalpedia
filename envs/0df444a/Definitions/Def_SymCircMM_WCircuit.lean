-- Prove2me | Definitions.Def_SymCircMM_WCircuit
-- name    : SymCircMM_WCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:36.305626+00:00
-- url     : https://prove2.me/theorems/71d8d3ec-2782-47fc-b4a2-280c2a0eed76
-- title:
--   Weighted circuits: scalars on the edges into $+$-gates, size, product gates, rigidity
-- statement:
--   A **weighted circuit** is an algebraic circuit whose edges into $+$-gates carry scalars of $F$, so that a $+$-gate $g$ computes
--
--   $$\hat g=\sum_{c}\mathrm{wire}(g,c)\,\mathrm{coef}(g,c)\,\hat c,$$
--
--   while input gates and $\times$-gates compute as in an ordinary circuit. This is the shape of the circuit $C'$ constructed in the proof of Proposition 4.2, whose addition gates combine their inputs "with the displayed constants on the edges".
--
--   The size of a weighted circuit is its number of edges with multiplicity, and $\mathrm{numMul}(C)$ is its number of $\times$-gates. An automorphism extending a map $\pi$ of the variables is an automorphism of the underlying circuit that also preserves the edge scalars. The circuit is **rigid** (Definition 2.3) if the only such automorphism that fixes every input gate (every variable gate and every constant gate) is the identity.
--
--   Rigidity makes the extension $\hat\sigma$ of each symmetry unique, so that the symmetry group acts on all gates.
--
--   **Formalization Note** The scalar $\mathrm{coef}(g,c)$ is fixed to $1$ on edges into input or $\times$-gates and on absent edges, so it carries information only on the edges of $+$-gates.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definition 2.3, p.4 (PDF p.5); Proposition 4.2 and its proof, p.10 (PDF p.11) and p.20 (PDF p.21)

import Mathlib
import Definitions.Def_SymCircMM_Circuit

set_option autoImplicit false

namespace SymCircMM

/-- A **weighted algebraic circuit**: an algebraic circuit (Definition 2.1) whose edges into `+`-gates
carry scalars of `F`, so that a `+`-gate computes an `F`-linear combination of its children. This is
the circuit `C′` built in the proof of Proposition 4.2 (Dahan, Dawar, Kush, Pago, *Symmetric Circuits
for Matrix Multiplication*, manuscript (sha256 999a7eba…), Appendix C, p.20 (PDF p.21): "with the
displayed constants on the edges").

**Formalization Note.** `coef g c` is the scalar on the edges from `c` into the `+`-gate `g`; it is
fixed to `1` on edges into other gates and on absent edges, so it carries no information there.
Size, symmetry and rigidity are as for circuits, with automorphisms also preserving the scalars. -/
structure WCircuit (F X γ : Type) [Field F] extends Circuit F X γ where
  /-- the scalar on the edges from `c` into the `+`-gate `g` -/
  coef : γ → γ → F
  /-- scalars only live on edges into `+`-gates -/
  coef_eq_one : ∀ g c, (label g).isLeaf = true ∨ (label g).isMul = true ∨ wire g c = 0 →
    coef g c = 1

namespace WCircuit

variable {F X γ : Type} [Field F]

/-- The polynomial computed by each gate of a weighted circuit: as for circuits, except that a
`+`-gate `g` computes `∑_c wire(g, c) · coef(g, c) · ĉ`. -/
noncomputable def val [Fintype γ] (C : WCircuit F X γ) : γ → MvPolynomial X F :=
  C.wf.fix fun g IH =>
    match C.label g with
    | .input x => MvPolynomial.X x
    | .const c => MvPolynomial.C c
    | .add => ∑ c, if h : C.wire g c = 0 then 0 else
        (C.wire g c : MvPolynomial X F) * MvPolynomial.C (C.coef g c) * IH c h
    | .mul => ∏ c, if h : C.wire g c = 0 then 1 else IH c h ^ C.wire g c

/-- The size of a weighted circuit: its number of edges counted with multiplicity. -/
def size [Fintype γ] (C : WCircuit F X γ) : ℕ := C.toCircuit.size

/-- The number of product (`×`) gates of a weighted circuit. -/
def numMul [Fintype γ] (C : WCircuit F X γ) : ℕ :=
  (Finset.univ.filter fun g => (C.label g).isMul = true).card

/-- `φ` is an automorphism of the weighted circuit extending the variable map `π`: an automorphism of
the underlying labelled multi-DAG (`Circuit.Extends`) that also preserves the edge scalars. -/
def Extends (C : WCircuit F X γ) (π : X → X) (φ : γ ≃ γ) : Prop :=
  C.toCircuit.Extends π φ ∧ ∀ g c, C.coef (φ g) (φ c) = C.coef g c

/-- **Rigidity** (Definition 2.3, p.4 (PDF p.5)): the only automorphism of the circuit that fixes every
input gate (variable or constant) is the identity. -/
def IsRigid (C : WCircuit F X γ) : Prop :=
  ∀ φ : γ ≃ γ, C.Extends id φ → (∀ g, (C.label g).isLeaf = true → φ g = g) → φ = Equiv.refl γ

end WCircuit

end SymCircMM


