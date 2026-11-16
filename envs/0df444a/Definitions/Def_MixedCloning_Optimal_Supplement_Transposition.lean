-- Prove2me | Definitions.Def_MixedCloning_Optimal_Supplement_Transposition
-- name    : MixedCloning_Optimal_Supplement_Transposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:15:32.877468+00:00
-- url     : https://prove2.me/theorems/1517e11f-d46b-4565-97bd-73ba6ff2087d
-- title:
--   Section 4 — transposers, the pure-state transposer, the PTT transposer, transposition sample complexity
-- statement:
--   This file adds the objects of Section 4 (mixed-state transposition) on top of the published model of the cloning mission (word-indexed tensor registers, squared fidelity $F$, tensor powers $X^{\otimes n}$, the symmetric projector $\Pi_{\mathrm{Sym}}^{(D,n)}$, $d[n]=\binom{n+d-1}{n}$, the random purification channel specification RPC, and the partial trace $\mathrm{Tr}_B$ over the purifying registers).
--
--   1. A **transposer** with $n$ inputs and $k$ outputs is a map from operators on $(\mathbb C^d)^{\otimes n}$ to operators on $(\mathbb C^d)^{\otimes k}$; transposition consumes the input, so there are $k$ output registers, not $n+k$.
--
--   2. **Partial trace over the first $n$ registers.** For an operator $Y$ on $(\mathbb C^D)^{\otimes(n+k)}$, $\mathrm{Tr}_{1..n}Y$ is the operator on the last $k$ registers, kept in order.
--
--   3. **The pure-state transposer** $T^{(D,n,k)}$. With $\Pi=\Pi_{\mathrm{Sym}}^{(D,n)}$, $\Pi'=\Pi_{\mathrm{Sym}}^{(D,n+k)}$ and a fixed state $\tau$ on $k$ registers,
--   $$T(X)=\frac{D[n]}{D[n+k]}\Bigl(\mathrm{Tr}_{1..n}\bigl[\Pi'\,\bigl((\Pi X\Pi)\otimes I^{\otimes k}\bigr)\bigr]\Bigr)^{\mathsf T}+\mathrm{tr}\bigl((I-\Pi)X\bigr)\,\tau ,$$
--   where ${}^{\mathsf T}$ is the full transpose in the computational (product) basis. This is the complementary channel of Werner's cloner, which the paper (p. 8) identifies with the optimal pure-state transposer of [BGSQ26]; on symmetric inputs it equals $X\mapsto D[n]\int \mathrm{tr}(X\,|u\rangle\langle u|^{\otimes n})\,(|\bar u\rangle\langle\bar u|)^{\otimes k}\,du$. The $\tau$ term extends the map off the symmetric subspace, exactly as the published Werner cloner does.
--
--   4. **The PTT transposer** (Figure 8): apply a random purification channel $R$ with purifying space $\mathbb C^r$, apply $T^{(dr,n,k)}$ on the alphabet $[d]\times[r]$ (product basis, $\mathbb C^d$ factor first), then trace out the purifying registers:
--   $$\mathrm{PTT}(X)=\mathrm{Tr}_B\bigl(T^{(dr,n,k)}(R(X))\bigr).$$
--
--   5. A map $T$ **transposes rank-$r$ states to fidelity $1-\varepsilon$** if it is a channel (linear, completely positive, trace preserving) and $F\bigl(T(\rho^{\otimes n}),(\rho^{\mathsf T})^{\otimes k}\bigr)\ge 1-\varepsilon$ for every state $\rho$ on $\mathbb C^d$ of rank at most $r$.
--
--   6. The **feasible sample counts** are the $n$ for which such a channel exists, and the **transposition sample complexity** is their infimum.
--
--   **Formalization Note** The transpose is Lean's `Matrix.transpose` in the computational basis; with the alphabet `Fin d × Fin r` it is the product-basis transpose, so the published `partialTrace` gives $\mathrm{Tr}_B(|\rho\rangle\langle\rho|^{\mathsf T})=\rho^{\mathsf T}$ (p. 26). The sample complexity is an `sInf` over `ℕ`, which is $0$ on the empty set; theorems using it assert the feasible set nonempty.
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 26, Section 4 and Figure 8; p. 8, Theorem 5 and footnote 4; p. 29, Theorem 27

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section

namespace MixedCloning.Optimal.Supplement

open Matrix MixedCloning.Optimal
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 4: a transposer takes n input registers to k output registers. -/
abbrev Transposer (d n k : ℕ) := QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d) k)

/-- Trace out the first n registers of an (n+k)-register operator, keeping the last k
in order (the register convention of `appendIdentity`). -/
def traceFirst {a : Type} [Fintype a] (n k : ℕ) (Y : Op (Word a (n+k))) : Op (Word a k) :=
  fun i j => ∑ z : Word a n, Y (Fin.append z i) (Fin.append z j)

/-- The optimal pure-state transposer of [BGSQ26], taken as the complement of Werner's
cloner: X ↦ (d[n]/d[n+k]) (Tr_{1..n}[Π_{n+k} (Π_n X Π_n ⊗ I^{⊗k})])ᵀ on the Bose corner,
extended by the fixed state tau on its complement. The transpose is the full transpose in
the computational (product) basis of the k output registers. -/
def wernerTransposer (a : Type) [Fintype a] (n k : ℕ) (tau : Op (Word a k)) :
    QAlgorithms.Superop (Word a n) (Word a k) := fun X =>
  let P := symProjector a n
  let Q := symProjector a (n+k)
  ((symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) •
    (traceFirst n k (Q * appendIdentity n k (P * X * P)))ᵀ + (((1-P) * X).trace) • tau

/-- Figure 8: random purification, the pure-state transposer on alphabet Fin d × Fin r,
then trace out B. -/
def ptt (d r n k : ℕ)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (tau : Op (Word (Fin d × Fin r) k)) : Transposer d n k :=
  fun X => partialTrace k (wernerTransposer (Fin d × Fin r) n k tau (R X))

/-- A channel producing (ρᵀ)^{⊗k} to fidelity 1 - eps from ρ^{⊗n}, for every state of
rank at most r. -/
def Transposes (d r n k : ℕ) (eps : ℝ) (T : Transposer d n k) : Prop :=
  QAlgorithms.IsChannel T ∧ ∀ rho : Op (Fin d), IsState rho → rho.rank ≤ r →
    1-eps ≤ fidelity (T (tensorPower n rho)) (tensorPower k rhoᵀ)

def transposeFeasibleSamples (d r k : ℕ) (eps : ℝ) : Set ℕ :=
  {n | ∃ T : Transposer d n k, Transposes d r n k eps T}

def transposeSampleComplexity (d r k : ℕ) (eps : ℝ) : ℕ :=
  sInf (transposeFeasibleSamples d r k eps)

end MixedCloning.Optimal.Supplement


