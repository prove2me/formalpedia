-- Prove2me | Definitions.Def_QiOPoQ_Supplement_Assumption62
-- name    : QiOPoQ_Supplement_Assumption62
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:07:49.134797+00:00
-- url     : https://prove2.me/theorems/40696f0b-d6fa-4456-9127-d7f2cb7f1db1
-- title:
--   Assumption 6.2 (quantum split-circuit pseudo-randomness)
-- statement:
--   For given functions $p_1,p_2$ (nonnegative, polynomially bounded, polynomial-time computable): for every polynomially bounded width $n$, every pair of polynomial-size families of ancilla-free $n$-qubit circuits $A,B$, every polynomially bounded $N_A,N_B,N_R$ with $N_A\ge p_1(\lambda,n)|A|$, $N_B\ge p_1(\lambda,n)|B|$, $N_R\ge p_2(\lambda,n)$, $N_A\ge|A|+N_R$, $N_B\ge|B|+N_R$, and every non-uniform QPT distinguisher $D$,
--
--   $$\big|\Pr[D(1^\lambda,X\|Y)=1]-\Pr[D(1^\lambda,Z)=1]\big|\le\mathrm{negl}(\lambda),$$
--
--   where $R\leftarrow\mathcal C_{n,N_R}$, $X\leftarrow\mathcal E_{A\|R,N_A}$, $Y\leftarrow\mathcal E_{R^\dagger\|B,N_B}$ and $Z\leftarrow\mathcal E_{A\|B,N_A+N_B}$.
--
--   **Formalization Note** $p_1,p_2$ are natural-number valued; the length conditions hold at every $\lambda$. The existential over $p_1,p_2$ is in the hypothesis of Theorem 6.6.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.2, p.31

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_NUQPT
import Definitions.Def_QiOPoQ_Supplement_Placement
import Definitions.Def_QMAvsQCMAH_PolyBounded
import Definitions.Def_QiOPoQ_Supplement_PolyBounded2
import Definitions.Def_QiOPoQ_Supplement_avgRand

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **Assumption 6.2 (Quantum split-circuit pseudo-randomness).** Gheorghiu, Gupte, Havlíček,
Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.2, p.31: "There are nonnegative polynomially
bounded and polynomial-time computable functions p1, p2 with the following property. For every
polynomially bounded width n = n(λ), every pair of polynomial-size families of n-qubit
ancilla-free unitary circuits A, B, every choice of polynomially bounded lengths N_A, N_B, N_R,
and every non-uniform QPT distinguisher D, |Pr[D(1^λ, X∥Y) → 1] − Pr[D(1^λ, Z) → 1]| ≤ negl(λ),
where X ← E_{A∥R,N_A}, Y ← E_{R†∥B,N_B}, R ← C_{n,N_R} and Z ← E_{A∥B,N_A+N_B}, whenever
N_A ≥ p1(λ, n) · |A|, N_B ≥ p1(λ, n) · |B|, N_R ≥ p2(λ, n), and (N_A, N_B, N_R) is admissible
for (A, B)."

This is the property of the given `p1, p2` (the existential is taken in the hypothesis of
Theorem 6.6). Admissibility (Notation 6.1, p.30): `N_A ≥ |A| + N_R` and `N_B ≥ |B| + N_R`.

**Formalization Note.** `p1, p2` are ℕ-valued (gate-count multipliers and lengths). The length
conditions are required at every `λ`. Ancilla-free `n`-qubit circuits are `afCirc` (all `n` wires
are the output, in order), so they are unitary; the distinguisher receives the description of the
sampled circuit. -/
def Assumption62 (G : GateSet) (p1 p2 : ℕ → ℕ → ℕ) : Prop :=
  PolyTime2 p1 ∧ PolyTime2 p2 ∧ PolyBounded2 p1 ∧ PolyBounded2 p2 ∧
  ∀ nw : ℕ → ℕ, QMAvsQCMAH.PolyBounded nw → ∀ A B : (l : ℕ) → List (Placement G (nw l)),
    QMAvsQCMAH.PolyBounded (fun l => (A l).length) → QMAvsQCMAH.PolyBounded (fun l => (B l).length) →
    ∀ NA NB NR : ℕ → ℕ, QMAvsQCMAH.PolyBounded NA → QMAvsQCMAH.PolyBounded NB → QMAvsQCMAH.PolyBounded NR →
    (∀ l, p1 l (nw l) * (A l).length ≤ NA l ∧ p1 l (nw l) * (B l).length ≤ NB l ∧
      p2 l (nw l) ≤ NR l ∧ (A l).length + NR l ≤ NA l ∧ (B l).length + NR l ≤ NB l) →
    ∀ D : NUQPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ l,
      |avgRand G (nw l) (NR l) (fun R =>
          avgEquiv G (nw l) (NA l) (A l ++ R) fun X =>
            avgEquiv G (nw l) (NB l) (afDagger R ++ B l) fun Y =>
              D.acc G l (encCirc (afCirc (nw l) (X ++ Y)))) -
        avgEquiv G (nw l) (NA l + NB l) (A l ++ B l) (fun Z =>
          D.acc G l (encCirc (afCirc (nw l) Z)))| ≤ μ l

end QiOPoQ.Supplement


