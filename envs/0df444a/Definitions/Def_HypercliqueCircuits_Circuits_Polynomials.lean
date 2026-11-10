-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Polynomials
-- name    : HypercliqueCircuits_Circuits_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:33:56.06109+00:00
-- url     : https://prove2.me/theorems/a0b54c81-0c2b-40dc-8ea1-70100baacc2f
-- title:
--   Hyperclique polynomials and computed matrix contractions
-- statement:
--   For dimensions $n_j$, a variable consists of an omitted coordinate $j$ and values of all the other coordinates. The rectangular hyperclique polynomial is
--
--   $$\Delta_{(n_1,\ldots,n_k)}^{(k)}=\sum_\alpha\prod_j x^{(j)}_{\alpha_{-j}}.$$
--
--   Its uniform specialization has all $n_j=n$. The size-only bound predicate asserts existence of actual circuits of size at most $C n^a$, with one positive $C$ before all positive $n$; it includes no generator or time assumption.
--
--   The module also defines every entry of a matrix product and the independent variables $U(i,z),V(j,z),X_s(i,j,z_{-s})$ for $k=r+3$. The matrices are $Q^z_{ij}=U(i,z)X_{k-2}(i,j,z_{-(k-2)})$ and $P^z_{ij}=V(j,z)\prod_{s=1}^{k-3}X_s(i,j,z_{-s})$. For a computed integer matrix kernel $T$, the twisted polynomial is
--
--   $$\Delta_{n,T}^{(k)}=\sum_z\langle P^z,TQ^z\rangle.$$
--
--   The pairing is bilinear. Neither contraction nor the final polynomial is supplied as a circuit input.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, §1.1, pp.3–4 (PDF 4–5); §2, p.16 (PDF 17); §§1.4 and 3.1, pp.11–13,17–18 (PDF 12–14,18–19).

import Definitions.Def_HypercliqueCircuits_Circuits_Arithmetic

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- The coordinates other than j, retaining their original order and labels. -/
abbrev Other {k : ℕ} (j : Fin k) := {i : Fin k // i ≠ j}
abbrev HVar {k : ℕ} (ns : Fin k → ℕ) := (j : Fin k) × ((i : Other j) → Fin (ns i.val))

noncomputable def hypercliqueOver (R : Type) [CommRing R] {k : ℕ}
    (ns : Fin k → ℕ) : MvPolynomial (HVar ns) R :=
  ∑ a : (i : Fin k) → Fin (ns i),
    ∏ j : Fin k, MvPolynomial.X ⟨j, fun i => a i.val⟩

noncomputable def hyperclique {k : ℕ} (ns : Fin k → ℕ) : MvPolynomial (HVar ns) ℚ :=
  hypercliqueOver ℚ ns

abbrev UniformVar (k n : ℕ) := HVar (fun _ : Fin k => n)

noncomputable def uniformHyperclique (k n : ℕ) : MvPolynomial (UniformVar k n) ℚ :=
  hyperclique (fun _ : Fin k => n)

noncomputable def uniformHypercliqueOver (R : Type) [CommRing R] (k n : ℕ) :
    MvPolynomial (UniformVar k n) R := hypercliqueOver R (fun _ : Fin k => n)

/-- The size-only inductive premise, with actual circuits over a fixed ring.
It asserts neither a uniform generator nor dyadic restriction on supplied constants. -/
def HasSizeBoundOver (R : Type) [CommRing R] (k : ℕ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ c : Circuit R (UniformVar k n) 1,
      c.polynomial id 0 = uniformHypercliqueOver R k n ∧
      (c.size : ℝ) ≤ C * (n : ℝ)^a

/-- Independent input matrices; output pointers are indexed by pairs (i,j). -/
abbrev MMVar (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

noncomputable def matrixProduct (R : Type) [CommRing R] (a b c : ℕ) (i : Fin a) (j : Fin c) :
    MvPolynomial (MMVar a b c) R :=
  ∑ h : Fin b, MvPolynomial.X (.inl (i,h)) * MvPolynomial.X (.inr (h,j))

/-- k = r+3; U and V omit j and i respectively; X_s omits z_s.
Using a sum type keeps these variable groups independent. -/
abbrev SplitVar (r : ℕ) (ι : Type) :=
  (ι × (Fin (r+1) → ι)) ⊕ ((ι × (Fin (r+1) → ι)) ⊕
    ((s : Fin (r+1)) × (ι × ι × (Other s → ι))))

noncomputable def U {R : Type} [CommRing R] {r : ℕ} {ι : Type} (i : ι) (z : Fin (r+1) → ι) :
    MvPolynomial (SplitVar r ι) R := MvPolynomial.X (.inl (i,z))
noncomputable def V {R : Type} [CommRing R] {r : ℕ} {ι : Type} (j : ι) (z : Fin (r+1) → ι) :
    MvPolynomial (SplitVar r ι) R := MvPolynomial.X (.inr (.inl (j,z)))
noncomputable def XV {R : Type} [CommRing R] {r : ℕ} {ι : Type} (s : Fin (r+1)) (i j : ι) (z : Other s → ι) :
    MvPolynomial (SplitVar r ι) R := MvPolynomial.X (.inr (.inr ⟨s,i,j,z⟩))

noncomputable def Q {R : Type} [CommRing R] {r : ℕ} {ι : Type} (z : Fin (r+1) → ι) (i j : ι) :
    MvPolynomial (SplitVar r ι) R :=
  U i z * XV (Fin.last r) i j (fun s => z s.val)

noncomputable def P {R : Type} [CommRing R] {r : ℕ} {ι : Type} (z : Fin (r+1) → ι) (i j : ι) :
    MvPolynomial (SplitVar r ι) R :=
  V j z * ∏ s : Fin r, XV s.castSucc i j (fun h => z h.val)

/-- Integer matrix kernels acting on matrix entries; the Frobenius pairing is bilinear. -/
abbrev Operator (ι : Type) := Matrix (ι × ι) (ι × ι) ℤ

noncomputable def applyOperator {ι : Type} [Fintype ι] (T : Operator ι)
    (M : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  fun i j => ∑ ab : ι × ι, T (i,j) ab * M ab.1 ab.2

noncomputable def twist (R : Type) [CommRing R] (r : ℕ) (ι : Type) [Fintype ι] (T : Operator ι) :
    MvPolynomial (SplitVar r ι) R :=
  ∑ z : Fin (r+1) → ι, ∑ i : ι, ∑ j : ι,
    P z i j * ∑ ab : ι × ι, MvPolynomial.C ((T (i,j) ab : ℤ) : R) * Q z ab.1 ab.2

end HypercliqueCircuits.Circuits


