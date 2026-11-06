-- Prove2me | Definitions.Def_BenignDegen_Boolean
-- name    : BenignDegen_Boolean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:57.674322+00:00
-- url     : https://prove2.me/theorems/21a84fd0-f8ec-49e4-8cc0-475231fc39c7
-- title:
--   Boolean moment relaxation $(\mathrm P_d)$, $\mathcal T_d,\mathcal R_d,\mathcal H_d$, $C_f$, $\mathcal S_\star$ (2.4), rank-one exactness (2.5), encoding (B.3), $\Psi_S$ (4.4)
-- statement:
--   Fix $1\le d\le n$. Monomials are indexed by $\mathcal I_d=\{T\subseteq[n]:|T|\le\min\{d,n\}\}$, $N=|\mathcal I_d|$, $b_d(x)=(x^T)_{T\in\mathcal I_d}$. For $\Gamma\in\mathcal I_{2d}$ the XOR-class matrix is $(A_\Gamma)_{A,B}=\mathbf 1\{A\triangle B=\Gamma\}$, and
--
--   $$
--   \mathcal H_d=\operatorname{span}\{A_\Gamma:\Gamma\in\mathcal I_{2d}\},\quad \mathcal T_d=\operatorname{span}\{A_\Gamma:\emptyset\ne\Gamma\in\mathcal I_{2d}\},\quad \mathcal R_d=\mathcal T_d^\perp .
--   $$
--
--   The moment matrix is $M_d(y)=\sum_{\Gamma}y_\Gamma A_\Gamma$, the moment body $\mathcal X_d=\{M_d(y):y_\emptyset=1,\ M_d(y)\succeq0\}$, $C_f=\sum_\Gamma f_\Gamma A_\Gamma/\|A_\Gamma\|_F^2$, and $(\mathrm P_d)$ minimizes $\langle C_f,X\rangle$ over $\mathcal X_d$. The Gram map is $\mathcal G_d(Y)=\sum_\Gamma\langle A_\Gamma,Y\rangle x^\Gamma$, and
--
--   $$
--   \mathcal S_\star=\{S\succeq0:\ b_d(x)^\top Sb_d(x)\equiv f-f_\star\ (\mathrm{mod}\ I_B)\},\qquad f_\star=\mathrm{OPT}(f)=\min_{x\in\{\pm1\}^n}f(x).
--   $$
--
--   The order $d$ is **uniquely rank-one exact** with minimizer $x_\star$ if $\operatorname{argmin}(\mathrm P_d)=\{b_d(x_\star)b_d(x_\star)^\top\}$, and a **strictly complementary certificate** is some $S\in\mathcal S_\star$ with $\operatorname{rank}S=N-1$. The module also defines the symmetric units $F_{A,B}$, reference pairs, the consistency matrices $D_{A,B}=F_{A,B}-F^\circ_\Gamma$, the independent encoding $\mathcal A_dX=(X_{\emptyset,\emptyset},\langle D_1,X\rangle,\dots,\langle D_{m-1},X\rangle)$, $b=e_1$ (B.3), the predicate "$\{X:\mathcal AX=b\}=I_N+\mathcal T_d$", and, with $q=b_d(x_\star)/\sqrt N$ and $V=q^\perp$, the maps
--
--   $$
--   \mathscr J_S(H)=h_{00}qq^\top+qw^\top+wq^\top,\quad h_{00}=q^\top Hq,\quad w=N(NI_N+\sigma S)^{-1}P_VHq,\qquad \Psi_S=\mathsf P\mathscr J_S+\mathsf P^\perp(\mathrm{Id}-\mathscr J_S).
--   $$
--
--   **Formalization Note** $\mathcal I_d$ is `{T : Finset (Fin n) // T.card ≤ d}`; a square-free $f$ is its coefficient function; $\{\pm1\}^n$ is `Fin n → ℤˣ`; the congruence mod $I_B$ is equality of square-free coefficients via $\mathcal G_d$; unordered pairs are `Sym2`. Symmetric arrays become elements of $\mathbb S^N$ through `SymMat.ofMat`, which returns a symmetric array unchanged; `SymMat.ofMat (Matrix.single A B 1)` is exactly $F_{A,B}$.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, (1.1) p.1; §2, (2.1)–(2.5), pp.4–5; Appendix B, (B.1)–(B.3), pp.14–15; §4, (4.4), p.9

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry

namespace BenignDegen

open SunNLSDP.Equiv Matrix
open scoped RealInnerProductSpace

noncomputable section

/-! # The Boolean quotient moment relaxation (§2), its Gram certificates, the independent
encoding (B.3), and the maps `J_S`, `Ψ_S` of (4.4)

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, (1.1) p.1; §2, (2.1)–(2.5), pp.4–5; Appendix B, (B.1)–(B.3), (B.6),
pp.14–15; §4, (4.4), p.9.

**Formalization Note** `I_d = {T ⊆ [n] : |T| ≤ min{d, n}}` is `{T : Finset (Fin n) // T.card ≤ d}`
(`|T| ≤ n` always). A square-free polynomial `f = Σ_Γ f_Γ x^Γ` is its coefficient function
`Finset (Fin n) → ℝ`; `deg f ≤ k` means `f_Γ = 0` for `|Γ| > k`. The cube `{±1}ⁿ` is
`Fin n → ℤˣ`. `b_d(x)^⊤ S b_d(x) ≡ g (mod I_B)` is the equality of square-free coefficients
`G_d(S) = g` (the map `G_d` of (B.2)), so `S_⋆` of (2.4) is
`{S ⪰ 0 : G_d(S)_Γ = f_Γ − [Γ = ∅] f_⋆ for all Γ}` with `f_⋆ = OPT(f)`. Matrices built from a
symmetric array use `SymMat.ofMat`, which returns the array itself when it is symmetric; in
particular `SymMat.ofMat (Matrix.single A B 1)` is the symmetric unit `F_{A,B}` of Appendix B
(`E_{A,A}` if `A = B`, `½(E_{A,B} + E_{B,A})` otherwise). Unordered pairs `{A, B}` are
`Sym2 I_d`. -/

/-- The index set `I_d` of (2.1). -/
abbrev Idx (n d : ℕ) : Type := {T : Finset (Fin n) // T.card ≤ d}

/-- `N_d := |I_d|` (2.1). -/
def Nd (n d : ℕ) : ℕ := Fintype.card (Idx n d)

/-- `I_{2d}`, as a finset of subsets of `[n]`. -/
def I2d (n d : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter (fun Γ => Γ.card ≤ 2 * d)

/-- The monomial `x^T := Π_{i∈T} x_i` at a cube point `x ∈ {±1}ⁿ`. -/
def mono {n : ℕ} (x : Fin n → ℤˣ) (T : Finset (Fin n)) : ℝ := ∏ i ∈ T, (((x i : ℤ)) : ℝ)

/-- The value `f(x) = Σ_T f_T x^T` of a square-free polynomial at a cube point. -/
def evalPoly {n : ℕ} (f : Finset (Fin n) → ℝ) (x : Fin n → ℤˣ) : ℝ := ∑ T, f T * mono x T

/-- `OPT(f) := min_{x∈{±1}ⁿ} f(x)` (1.1). -/
def cubeMin {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (evalPoly f)

/-- `deg f ≤ k`: every monomial of `f` has degree at most `k`. -/
def DegLe {n : ℕ} (f : Finset (Fin n) → ℝ) (k : ℕ) : Prop := ∀ T : Finset (Fin n), k < T.card → f T = 0

/-- `b_d(x) := (x^T)_{T ∈ I_d} ∈ ℝ^{N_d}` (2.1). -/
def bvec (n d : ℕ) (x : Fin n → ℤˣ) : EuclideanSpace ℝ (Idx n d) :=
  WithLp.toLp 2 (fun T => mono x T.1)

/-- The rank-one matrix `uu^⊤`. -/
def rankOne {ι : Type} [Fintype ι] [DecidableEq ι] (u : EuclideanSpace ℝ ι) : SymMat ι :=
  SymMat.ofMat (Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u))

/-- The identity `I_N` as an element of `S^N`. -/
def IdMat (ι : Type) [Fintype ι] [DecidableEq ι] : SymMat ι := SymMat.ofMat 1

/-- The XOR-class matrix `(A_Γ)_{A,B} := 1{A △ B = Γ}`, `A, B ∈ I_d` (p.4). -/
def xorMat (n d : ℕ) (Γ : Finset (Fin n)) : SymMat (Idx n d) :=
  SymMat.ofMat (fun A B => if symmDiff A.1 B.1 = Γ then 1 else 0)

/-- `H_d := span{A_Γ : Γ ∈ I_{2d}}` (B.1). -/
def Hd (n d : ℕ) : Submodule ℝ (SymMat (Idx n d)) :=
  Submodule.span ℝ (xorMat n d '' (I2d n d : Set (Finset (Fin n))))

/-- `T_d := span{A_Γ : ∅ ≠ Γ ∈ I_{2d}}` (B.1). -/
def Td (n d : ℕ) : Submodule ℝ (SymMat (Idx n d)) :=
  Submodule.span ℝ (xorMat n d '' {Γ | Γ ∈ I2d n d ∧ Γ ≠ ∅})

/-- `R_d := T_d^⊥` (B.1). -/
def Rd (n d : ℕ) : Submodule ℝ (SymMat (Idx n d)) := (Td n d)ᗮ

/-- The moment matrix `M_d(y) := Σ_{Γ ∈ I_{2d}} y_Γ A_Γ` (2.2). -/
def momentMat (n d : ℕ) (y : Finset (Fin n) → ℝ) : SymMat (Idx n d) :=
  ∑ Γ ∈ I2d n d, y Γ • xorMat n d Γ

/-- The moment body `X_d := {M_d(y) : y_∅ = 1, M_d(y) ⪰ 0}` (p.4). -/
def momentBody (n d : ℕ) : Set (SymMat (Idx n d)) :=
  {X | ∃ y : Finset (Fin n) → ℝ, y ∅ = 1 ∧ X = momentMat n d y ∧ X ∈ psdCone (Idx n d)}

/-- The canonical representative `C_f := Σ_Γ f_Γ A_Γ / ‖A_Γ‖²_F` (p.4), `Γ ∈ I_{2d}`. -/
def Cf (n d : ℕ) (f : Finset (Fin n) → ℝ) : SymMat (Idx n d) :=
  ∑ Γ ∈ I2d n d, (f Γ / ‖xorMat n d Γ‖ ^ 2) • xorMat n d Γ

/-- `argmin(P_d)`: the minimizers of `⟨C_f, X⟩` over `X_d` (2.3). -/
def argminPd (n d : ℕ) (f : Finset (Fin n) → ℝ) : Set (SymMat (Idx n d)) :=
  {X | X ∈ momentBody n d ∧ ∀ Y ∈ momentBody n d, ⟪Cf n d f, X⟫ ≤ ⟪Cf n d f, Y⟫}

/-- The Gram-to-polynomial map `G_d(Y) := Σ_{Γ ∈ I_{2d}} ⟨A_Γ, Y⟩ x^Γ` (B.2), as the coefficient
function of the square-free polynomial (zero outside `I_{2d}`). -/
def Gd (n d : ℕ) (Y : SymMat (Idx n d)) : Finset (Fin n) → ℝ :=
  fun Γ => if Γ ∈ I2d n d then ⟪xorMat n d Γ, Y⟫ else 0

/-- The Gram certificates `{S ⪰ 0 : b_d(x)^⊤ S b_d(x) ≡ f − f_⋆ (mod I_B)}` (2.4), with the
congruence read coefficientwise through `G_d`. With `f_⋆ = OPT(f)` this is `S_⋆` of (2.4). -/
def gramCerts (n d : ℕ) (f : Finset (Fin n) → ℝ) (fstar : ℝ) : Set (SymMat (Idx n d)) :=
  {S | S ∈ psdCone (Idx n d) ∧ Gd n d S = fun Γ => f Γ - if Γ = ∅ then fstar else 0}

/-- Unique rank-one exactness at order `d` with minimizer `x_⋆` (2.5):
`argmin(P_d) = {b_d(x_⋆) b_d(x_⋆)^⊤}`. -/
def UniqueRankOneOpt (n d : ℕ) (f : Finset (Fin n) → ℝ) (x : Fin n → ℤˣ) : Prop :=
  argminPd n d f = {rankOne (bvec n d x)}

/-- A strictly complementary optimal SOS certificate exists (p.5): some `S ∈ S_⋆` (2.4) with
`rank S = N − 1`. -/
def HasSCCertificate (n d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ S ∈ gramCerts n d f (cubeMin f), S.toMat.rank = Nd n d - 1

/-- An equality encoding of `(P_d)` with feasible affine set `{X : AX = b} = I_N + T_d`, the
first identity of (B.4); the cost of the encoded SDP is `C = C_f`. -/
def IsBoolEncoding {n d : ℕ} {κ : Type} [Fintype κ] (D : SDPData (Idx n d) κ) : Prop :=
  {X | D.A X = D.b} = {X | X - IdMat (Idx n d) ∈ Td n d}

/-! ### The independent equality encoding (B.3) -/

/-- The symmetric unit `F_{A,B}` (Appendix B): `E_{A,A}` if `A = B`, `½(E_{A,B} + E_{B,A})`
otherwise. -/
def symUnit {n d : ℕ} (A B : Idx n d) : SymMat (Idx n d) := SymMat.ofMat (Matrix.single A B 1)

lemma symUnit_comm {n d : ℕ} (A B : Idx n d) : symUnit A B = symUnit B A := by
  apply Subtype.ext
  simp only [symUnit, SymMat.ofMat]
  congr 1
  funext p
  rw [add_comm]
  simp only [Matrix.single_apply]
  grind

/-- `F_{A,B}` for an unordered pair `{A, B}`. -/
def symUnitP {n d : ℕ} (p : Sym2 (Idx n d)) : SymMat (Idx n d) :=
  Sym2.lift ⟨fun A B => symUnit A B, symUnit_comm⟩ p

/-- The XOR class `A △ B` of an unordered pair `{A, B}`. -/
def xorOf {n d : ℕ} (p : Sym2 (Idx n d)) : Finset (Fin n) :=
  Sym2.lift ⟨fun A B => symmDiff A.1 B.1, fun _ _ => symmDiff_comm _ _⟩ p

/-- `∅ ∈ I_d`. -/
def emptyIdx (n d : ℕ) : Idx n d := ⟨∅, by simp⟩

/-- A choice of one reference pair per XOR class (Appendix B): the pair chosen for the class
`Γ = A △ B` lies in that class, and the pair chosen for `Γ = ∅` is `{∅, ∅}`. -/
def IsRefChoice {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) : Prop :=
  (∀ p : Sym2 (Idx n d), xorOf (ref (xorOf p)) = xorOf p) ∧
    ref ∅ = s(emptyIdx n d, emptyIdx n d)

/-- The non-reference pairs, indexing the consistency matrices `D_1, …, D_{m−1}`. -/
abbrev NonRef {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) : Type :=
  {p : Sym2 (Idx n d) // p ≠ ref (xorOf p)}

/-- The row index set of (B.3): `none` is the normalization row `X_{∅,∅}`, `some p` the
consistency row of the non-reference pair `p`. -/
abbrev B3Row {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) : Type := Option (NonRef ref)

/-- The consistency matrix `D_{A,B} := F_{A,B} − F°_Γ`, `Γ = A △ B` (Appendix B). -/
def consistencyMat {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) (p : NonRef ref) :
    SymMat (Idx n d) :=
  symUnitP p.1 - symUnitP (ref (xorOf p.1))

/-- The row matrices of (B.3): `F_{∅,∅}` (so `⟨F_{∅,∅}, X⟩ = X_{∅,∅}`) and the `D_j`. -/
def rowMat {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) :
    B3Row ref → SymMat (Idx n d)
  | none => symUnit (emptyIdx n d) (emptyIdx n d)
  | some p => consistencyMat ref p

/-- The independent encoding `A_d X := (X_{∅,∅}, ⟨D_1, X⟩, …, ⟨D_{m−1}, X⟩)` (B.3). -/
def encB3 {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) :
    SymMat (Idx n d) →L[ℝ] EuclideanSpace ℝ (B3Row ref) :=
  ∑ r : B3Row ref, (innerSL ℝ (rowMat ref r)).smulRight (EuclideanSpace.single r (1 : ℝ))

/-- `b := e_1` (B.3): the unit vector of the normalization row. -/
def e1 {n d : ℕ} (ref : Finset (Fin n) → Sym2 (Idx n d)) : EuclideanSpace ℝ (B3Row ref) :=
  EuclideanSpace.single none 1

/-! ### The §4 objects `q`, `V = q^⊥`, `J_S`, `Ψ_S` (4.4) -/

/-- `q := u/√N`, `u = b_d(x_⋆)` (p.5). -/
def qvec (n d : ℕ) (x : Fin n → ℤˣ) : EuclideanSpace ℝ (Idx n d) :=
  (1 / Real.sqrt (Nd n d)) • bvec n d x

/-- `V := q^⊥ ⊆ ℝ^N` (p.5, §4). -/
def Vq (n d : ℕ) (x : Fin n → ℤˣ) : Submodule ℝ (EuclideanSpace ℝ (Idx n d)) :=
  (ℝ ∙ qvec n d x)ᗮ

/-- `J_S(H) := h₀₀ qq^⊤ + qw^⊤ + wq^⊤`, `h₀₀ := q^⊤Hq`, `w := N(NI_N + σS)^{-1}P_V Hq` (4.4). -/
def Jmap (n d : ℕ) (x : Fin n → ℤˣ) (σ : ℝ) (S H : SymMat (Idx n d)) : SymMat (Idx n d) :=
  let q : Idx n d → ℝ := WithLp.ofLp (qvec n d x)
  let h00 : ℝ := q ⬝ᵥ (H.toMat *ᵥ q)
  let w : Idx n d → ℝ := ((Nd n d : ℝ) • ((Nd n d : ℝ) • (1 : Matrix (Idx n d) (Idx n d) ℝ)
      + σ • S.toMat)⁻¹) *ᵥ ((projMat (Vq n d x) * H.toMat) *ᵥ q)
  SymMat.ofMat (h00 • Matrix.vecMulVec q q + Matrix.vecMulVec q w + Matrix.vecMulVec w q)

/-- `Ψ_S := P J_S + P^⊥(Id − J_S)` (4.4), with `P`, `P^⊥` the projectors of the encoding `D`. -/
def Psi {n d : ℕ} {κ : Type} [Fintype κ] (D : SDPData (Idx n d) κ) (x : Fin n → ℤˣ) (σ : ℝ)
    (S H : SymMat (Idx n d)) : SymMat (Idx n d) :=
  D.P (Jmap n d x σ S H) + D.Pperp (H - Jmap n d x σ S H)

/-- The matrix `Q_K` whose columns are the vectors `Q_1, …, Q_k ∈ ℝ^N`. -/
def colMat {ι : Type} [Fintype ι] {k : ℕ} (Q : Fin k → EuclideanSpace ℝ ι) : Matrix ι (Fin k) ℝ :=
  fun i j => WithLp.ofLp (Q j) i

/-- The term `Q_K Π₊(Q_K^⊤ H Q_K) Q_K^⊤` of (E.3), with `Π₊` the PSD projection on `S^k`. -/
def compressPlus {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (Q : Fin k → EuclideanSpace ℝ ι)
    (H : SymMat ι) : SymMat ι :=
  SymMat.ofMat (colMat Q * (PiPlus (SymMat.ofMat ((colMat Q)ᵀ * H.toMat * colMat Q))).toMat *
    (colMat Q)ᵀ)

end

end BenignDegen


