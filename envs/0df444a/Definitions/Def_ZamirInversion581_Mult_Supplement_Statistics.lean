-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Supplement_Statistics
-- name    : ZamirInversion581_Mult_Supplement_Statistics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:44.896545+00:00
-- url     : https://prove2.me/theorems/0ae9aa98-620c-4e50-bc39-74eab622a2a7
-- title:
--   Rank profiles, normalized laws, and ambiguity subgroups
-- statement:
--   Let $F$ be a finite field, $q=|F|$, and let $n$ be a matrix dimension. Uniform finite probabilities and expectations use the published uniform-average definition. Put
--   $$
--   s_{q,n}=\Pr_X[\det X=0],\qquad \pi_j=\Pr_X[\operatorname{rank}X=n-j],\qquad b_{\rm rank}=\max_{0\le r\le n}\Pr_X[\operatorname{rank}X=r],
--   $$
--   where $X$ is uniform on all $n\times n$ matrices. For a profile $b_0,\ldots,b_n\in\mathbb R^m$ and a subspace $V\le F^n$, set
--   $$
--   g_V(j)=\mathbb E_{W:\dim W=n-j}[b_{j+\dim(V\cap W)}],\qquad J=\left\lceil\frac{\log(100/\eta)}{\log q}\right\rceil.
--   $$
--   The maximum norm is the maximum of the absolute coordinates together with zero; hence it is zero when $m=0$. Profiles are extended by zero outside $0,\ldots,n$ only to make the definition total; the lemma never uses those indices. A subspace average on an empty set is zero, but every dimension used by the lemma has a nonempty Grassmannian.
--
--   For any randomized map $D:F^{n\times n}\to\operatorname{PMF}(F)$, let
--   $$
--   P=\operatorname{Law}(D(Y)/\det Y),\qquad P_A=\operatorname{Law}(D(RA)/\det R),
--   $$
--   where $Y,R$ are uniform invertible matrices with independent algorithm coins. For $a\in F^\times$, $aQ$ is the law of $aZ$ for $Z\sim Q$; it fixes zero. Write $\|P-Q\|_\infty=\max_{z\in F}|P(z)-Q(z)|$. With $\rho=\varepsilon^2/10000$, define
--   $$
--   S=\{a\in F^\times:\widehat P(a)\ge\varepsilon/2,\ \|\widehat P-a\widehat P\|_\infty\le6\rho\},\qquad H=\langle S\rangle.
--   $$
--   Finally $zH=\{zh:h\in H\}$ as a subset of $F$, so $0H=\{0\}$. These are unconditional finite probability and group objects, shared by all three supporting lemmas.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.3, 13–14, 19–22, rank probabilities, §3.3 display (1), §4.2 normalized laws, §4.4 displays (4)–(5). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-! Finite rank profiles (§3.3, pp.13–15) and normalized laws (§4.2–4.4, pp.19–22).
The source is Zamir, STOC 2027 #581, pinned PDF 175df18b…917.
No machine or trapdoor assumption enters these objects. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Mat (F : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) F

noncomputable def singularity (F : Type*) [Field F] [Fintype F] (n : ℕ) : ℝ :=
  unifProb (fun X : Mat F n => X.det = 0)

noncomputable def rankMass (F : Type*) [Field F] [Fintype F] (n r : ℕ) : ℝ :=
  unifProb (fun X : Mat F n => X.rank = r)

noncomputable def corankMass (F : Type*) [Field F] [Fintype F] (n j : ℕ) : ℝ :=
  rankMass F n (n - j)

noncomputable def rankBaseline (F : Type*) [Field F] [Fintype F] (n : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty
    (fun r => rankMass F n r)

/-- Sup norm including the zero-dimensional case. -/
noncomputable def maxNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (fun i => |x i|))).sup' (by simp) id

/-- Uniform subspaces; `Fintype.ofFinite` supplies only the canonical finite enumeration. -/
noncomputable def subspaces (F : Type*) [Field F] [Fintype F] (n k : ℕ) :
    Finset (Submodule F (Fin n → F)) := by
  classical
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  exact Finset.univ.filter (fun W => Module.finrank F W = k)

/-- Total extension of a profile by zero; only indices at most n occur in the lemma. -/
def profileAt {n m : ℕ} (b : Fin (n + 1) → Fin m → ℝ) (j : ℕ) : Fin m → ℝ :=
  if h : j < n + 1 then b ⟨j, h⟩ else 0

/-- Display (1): average over subspaces W of dimension n-j, coordinate by coordinate. -/
noncomputable def maskedProfile {n m : ℕ} (b : Fin (n + 1) → Fin m → ℝ)
    (V : Submodule F (Fin n → F)) (j : ℕ) : Fin m → ℝ :=
  fun i => (∑ W ∈ subspaces F n (n - j),
    profileAt b (j + Module.finrank F (V ⊓ W : Submodule F (Fin n → F))) i) / ((subspaces F n (n - j)).card : ℝ)

/-- Natural ceiling of the positive base-q logarithm in Lemma 3.4. -/
noncomputable def cutoff (F : Type*) [Fintype F] (η : ℝ) : ℕ :=
  ⌈Real.log (100 / η) / Real.log (Fintype.card F : ℝ)⌉₊

/-- Multiplication action on probability laws; zero is fixed. -/
noncomputable def shift (a : Fˣ) (P : PMF F) : PMF F :=
  P.map (fun x => (a : F) * x)

noncomputable def mass (P : PMF F) (z : F) : ℝ := (P z).toReal

/-- Finite maximum, rather than an unbounded real supremum. -/
noncomputable def distLaw (P Q : PMF F) : ℝ :=
  (Finset.univ : Finset F).sup' Finset.univ_nonempty (fun z => |mass P z - mass Q z|)

/-- Law of D(Y)/det Y for uniform invertible Y, independent D coins. -/
noncomputable def normalized {n : ℕ} (D : Mat F n → PMF F) : PMF F :=
  (PMF.uniformOfFintype (GL (Fin n) F)).bind fun Y =>
    (D (Y : Mat F n)).map (fun z => z / (Y : Mat F n).det)

/-- Law of D(RA)/det R for uniform invertible R. -/
noncomputable def maskedLaw {n : ℕ} (D : Mat F n → PMF F) (A : Mat F n) : PMF F :=
  (PMF.uniformOfFintype (GL (Fin n) F)).bind fun R =>
    (D ((R : Mat F n) * A)).map (fun z => z / (R : Mat F n).det)

/-- Display (5), including its heavy-atom condition. -/
noncomputable def nearSymmetries (ε : ℝ) (P : PMF F) : Set Fˣ :=
  {a | ε / 2 ≤ mass P (a : F) ∧ distLaw P (shift a P) ≤ 6 * (ε ^ 2 / 10000)}

noncomputable def ambiguity (ε : ℝ) (P : PMF F) : Subgroup Fˣ :=
  Subgroup.closure (nearSymmetries ε P)

/-- Multiplicative coset as a subset of F; the singular coset is {0}. -/
def fieldCoset (H : Subgroup Fˣ) (z : F) : Set F :=
  {w | ∃ h : H, w = z * (h.val : F)}

end ZamirInversion581.Mult.Supplement


