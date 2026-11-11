-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_WideWalk
-- name    : ExpanderWalkDecode_Main_WideWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:30.555147+00:00
-- url     : https://prove2.me/theorems/56cedd81-bc2d-45f6-b8d5-76c53c2f7687
-- title:
--   The $s$-wide replacement walk and the operator-variance quantities of Appendix B.6
-- statement:
--   Fix an outer graph $A$ whose ports are $\mathbb F_2^m$ (so it is $2^m$-regular, with neighbour map $\varphi$), and an inner Cayley graph $B$ on $\mathbb F_2^{ms}$ with generators $u_1,\dots,u_q$. An element $b\in B$ is viewed as $s$ blocks $b=(b[1],\dots,b[s])\in(\mathbb F_2^m)^s$; its first block is $\hat b=b[1]$, and $\mathrm{shift}(b[1],\dots,b[s])=(b[2],\dots,b[s],b[1])$.
--
--   A **wide replacement walk** with $k$ edges draws $a_0\in A$ and $b_1\in B$ uniformly, then $b_{i+1}=\mathrm{shift}(b_i+u_{j_i})$ for independent uniform generator indices $j_i$, and sets $a_i=\varphi(a_{i-1},\hat b_i)$ for $i=1,\dots,k$; it outputs $(a_0,\dots,a_k)$. Expectations $\mathbb E_{\vec a\sim\mathrm{WRW}^k_s}$ are taken over this sampling process (its full law, with multiplicities). $\mathrm{WRW}^k_s(a,b)$ denotes the walk conditioned on $(a_0,b_1)=(a,b)$, and $\overleftarrow{\mathrm{WRW}}{}^r_s(a,b)$ the walk with $r\ge1$ edges conditioned on its end $(a_r,b_r)=(a,b)$. The *set* $\mathrm{WRW}^k_s$ of Definition 5 is the set of walks that occur; $\mathrm{WRW}^{\le t}_s$ is the union over $k\le t$ together with the empty walk $\emptyset$, and $\mathrm{WRW}^{\le t}_s(a)$ consists of its nonempty walks starting at $a$.
--
--   For matrices $U_a\in\mathbb R^{D\times D}$ and $U_{\vec a}=U_{a_0}\cdots U_{a_k}$, Appendix B.6 defines
--   $$f_k(a,b)=\mathbb E_{\vec a\sim\mathrm{WRW}^k_s(a,b)}[U_{\vec a}],\quad M_k(a)=\mathbb E_b f_k(a,b),\quad M_k=\mathbb E_{a,b}f_k(a,b),$$
--   $$\tau_k^2=\big\|\mathbb E_{a,b}[f_k^{\mathsf T}f_k]-M_k^{\mathsf T}M_k\big\|_{\mathrm{op}},\quad \mu_k^2=\big\|\mathbb E_a[M_k(a)^{\mathsf T}M_k(a)]\big\|_{\mathrm{op}},\quad \Phi_k=\mu_k^2+\lambda^2\tau_k^2,$$
--   and, with $g_{r,k}(a,b)=\mathbb E_{\vec a\sim\overleftarrow{\mathrm{WRW}}{}^r_s(a,b)}[U_{a_{r-1}}\cdots U_{a_0}M_k(a_0)]$, the analogous $N_{r,k}(a)$, $N_{r,k}$, $\sigma_{r,k}^2$ and $\Psi_{r,k}=\|N_{r,k}\|_{\mathrm{op}}^2+\lambda^2\sigma_{r,k}^2$. Finally $H(s,t)=2\,(1/(9\lambda^4))^{1+t/s}(19\lambda^2)^t$.
--
--   **Formalization Note** The latent randomness of a walk with $k$ edges is $(a_0,b_1,j)\in A\times B\times[q]^k$; the indices $j_1,\dots,j_{k-1}$ are used and the last one is drawn but unused, which changes no expectation. The reverse walk is the forward walk conditioned on its end, as in the source's definition of $\overleftarrow{\mathrm{WRW}}{}^r_s(a,b)$ as the walks with $(a_r,b_r)=(a,b)$. Since every suffix of a wide replacement walk is again one, $\mathrm{WRW}^{\le t}_s$ is written as the set of all suffixes of walks with at most $t$ edges, which makes closure under dropping the first vertex structural.
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), pp. 22–27 (Appendix B.2–B.4, Definition 5, B.6)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Classical Matrix

/-!
# The s-wide replacement walk and the quantities of Appendix B.6

Source: Appendix B.2–B.4 and B.6 (pp. 22–27), Definition 5 (p. 23).

The inner graph `B` is a Cayley graph on `F₂^{ms}`, whose elements are viewed as `s` blocks of `m`
bits: `Inner m s = Fin s → Fin m → ZMod 2`, with generator family `u : Fin q → Inner m s`. The
shift rotates the blocks, `shift (b[1], …, b[s]) = (b[2], …, b[s], b[1])`, and `b̂ = b[1]` is the
first block. The outer graph `A` has port set `F₂^m` (degree `d = 2^m`), so `b̂` names a port.

A wide replacement walk with `k` edges (`k+1` outer vertices) draws `a₀ ∈ A` and `b₁ ∈ B`
uniformly and `b_{i+1} ∈ shift ∘ N(b_i)` (that is `b_{i+1} = shift (b_i + u_{j_i})` for a uniform
generator index `j_i`), and sets `a_i = φ(a_{i-1}, b̂_i)`. The latent space of the walk with `k`
edges is `Latent k = A × B × (Fin k → Fin q)`: the generator indices `j_1, …, j_{k-1}` are the
first `k-1` coordinates of the last component, and its last coordinate (when `k ≥ 1`) is drawn but
unused, which changes no expectation. Expectations over `WRW^k_s` are uniform averages over this
latent space: the full pushforward law, with multiplicities. The *set* `WRW^k_s` (Definition 5) is
the image of the latent space, a set of lists of outer vertices; `WRW^{≤t}_s` is the union over
`k ≤ t` together with the empty walk; since every suffix of a wide replacement walk is again one,
it is written as the set of all suffixes of the walks with at most `t` edges.
-/

/-- The inner vertex set `F₂^{ms}`, as `s` blocks of `m` bits. -/
abbrev Inner (m s : ℕ) := Fin s → Fin m → ZMod 2

/-- The shift operator `(b[1], …, b[s]) ↦ (b[2], …, b[s], b[1])`. -/
def shift {m s : ℕ} (b : Inner m s) : Inner m s := fun i => b (finRotate s i)

/-- The inverse shift `(b[1], …, b[s]) ↦ (b[s], b[1], …, b[s-1])`. -/
def shiftInv {m s : ℕ} (b : Inner m s) : Inner m s := fun i => b ((finRotate s).symm i)

/-- The first block `b̂ = b[1] ∈ F₂^m` (`0` when `s = 0`). -/
def hat {m s : ℕ} (b : Inner m s) : Fin m → ZMod 2 := if h : 0 < s then b ⟨0, h⟩ else 0

/-- The latent randomness of a wide replacement walk with `k` edges. -/
abbrev Latent (A : Type) (m s q k : ℕ) := A × Inner m s × (Fin k → Fin q)

section Walks

variable {A : Type} {m s q : ℕ}

/-- The `i`-th generator drawn, `u_{j_{i+1}}`, or `0` past the end. -/
def genAt {k : ℕ} (u : Fin q → Inner m s) (js : Fin k → Fin q) (i : ℕ) : Inner m s :=
  if h : i < k then u (js ⟨i, h⟩) else 0

/-- The inner walk `b₁, b₂, …` (index `0` is `b₁`): `b_{i+1} = shift (b_i + u_{j_i})`. -/
def bseq {k : ℕ} (u : Fin q → Inner m s) (b : Inner m s) (js : Fin k → Fin q) : ℕ → Inner m s
  | 0 => b
  | i + 1 => shift (bseq u b js i + genAt u js i)

/-- The outer walk `a₀, a₁, …`: `a_{i+1} = φ(a_i, b̂_{i+1})`. -/
def aseq {k : ℕ} (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (a : A) (b : Inner m s)
    (js : Fin k → Fin q) : ℕ → A
  | 0 => a
  | i + 1 => G.nbr (aseq G u a b js i) (hat (bseq u b js i))

/-- The wide replacement walk `(a₀, …, a_k)` with `k` edges determined by the latent point `l`. -/
def walk {k : ℕ} (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (l : Latent A m s q k) :
    Fin (k + 1) → A :=
  fun i => aseq G u l.1 l.2.1 l.2.2 i

/-- The walk as a list of outer vertices. -/
def walkList {k : ℕ} (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s)
    (l : Latent A m s q k) : List A :=
  List.ofFn (walk G u l)

variable [Fintype A]

/-- `E_{⃗a ∼ WRW^k_s} [F(⃗a)]`: the average over the latent space. -/
noncomputable def wrwAvg {M : Type} [AddCommGroup M] [Module ℝ M] (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) (k : ℕ) (F : (Fin (k + 1) → A) → M) : M :=
  avg fun l : Latent A m s q k => F (walk G u l)

/-- `E_{⃗a ∼ WRW^k_s(a, b)} [F(⃗a)]`: the walk conditioned on `(a₀, b₁) = (a, b)`. -/
noncomputable def fwdCond {M : Type} [AddCommGroup M] [Module ℝ M] (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) (k : ℕ) (F : (Fin (k + 1) → A) → M) (a : A) (b : Inner m s) : M :=
  avg fun js : Fin k → Fin q => F (walk G u (a, b, js))

/-- `E_{⃗a ∼ ←WRW^r_s(a, b)} [F(⃗a)]`: the walk with `r ≥ 1` edges conditioned on its end
`(a_r, b_r) = (a, b)` (`b_r` is index `r - 1` of `bseq`). -/
noncomputable def revCond {M : Type} [AddCommGroup M] [Module ℝ M] (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) (r : ℕ) (F : (Fin (r + 1) → A) → M) (a : A) (b : Inner m s) : M :=
  favg (Finset.univ.filter fun l : Latent A m s q r =>
      walk G u l (Fin.last r) = a ∧ bseq u l.2.1 l.2.2 (r - 1) = b)
    (fun l => F (walk G u l))

/-- The set `WRW^k_s` of walks with `k` edges (Definition 5). -/
noncomputable def wrwSet (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (k : ℕ) :
    Finset (List A) :=
  Finset.univ.image fun l : Latent A m s q k => walkList G u l

/-- The set `WRW^{≤t}_s`: the empty walk and every walk with at most `t` edges (written as all
suffixes of such walks, a set closed under `tail`). -/
noncomputable def wrwLe (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ) :
    Finset (List A) :=
  insert [] (Finset.univ.biUnion fun k : Fin (t + 1) =>
    Finset.univ.biUnion fun l : Latent A m s q k => (walkList G u l).tails.toFinset)

/-- `WRW^{≤t}_s(a)`: the nonempty walks of `WRW^{≤t}_s` starting at `a`. -/
noncomputable def wrwFrom (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ) (a : A) :
    Finset (List A) :=
  (wrwLe G u t).filter fun w => w.head? = some a

theorem nil_mem_wrwLe (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ) :
    [] ∈ wrwLe G u t := Finset.mem_insert_self _ _

theorem tail_mem_wrwLe (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ)
    {w : List A} (hw : w ∈ wrwLe G u t) : w.tail ∈ wrwLe G u t := by
  unfold wrwLe at hw ⊢
  rcases Finset.mem_insert.1 hw with h | h
  · subst h; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset,
      List.mem_tails] at h ⊢
    obtain ⟨k, l, hl⟩ := h
    exact ⟨k, l, (List.tail_suffix w).trans hl⟩

theorem walkList_mem_wrwLe (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ)
    (l : Latent A m s q t) : walkList G u l ∈ wrwLe G u t := by
  unfold wrwLe
  apply Finset.mem_insert_of_mem
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_tails]
  exact ⟨Fin.last t, l, List.suffix_refl _⟩

end Walks

section Amplification

variable {A : Type} [Fintype A] {m s q D : ℕ}

/-- `U_{⃗a} = U_{a₀} U_{a₁} ⋯ U_{a_k}`. -/
def prodU (U : A → Matrix (Fin D) (Fin D) ℝ) {k : ℕ} (w : Fin (k + 1) → A) :
    Matrix (Fin D) (Fin D) ℝ :=
  (List.ofFn fun i => U (w i)).prod

/-- `U_{a_{r-1}} ⋯ U_{a₀}` for `⃗a = (a₀, …, a_r)`. -/
def revProdU (U : A → Matrix (Fin D) (Fin D) ℝ) {r : ℕ} (w : Fin (r + 1) → A) :
    Matrix (Fin D) (Fin D) ℝ :=
  ((List.ofFn fun i : Fin r => U (w (Fin.castSucc i))).reverse).prod

variable (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (U : A → Matrix (Fin D) (Fin D) ℝ)

/-- `f_k(a, b) = E_{⃗a ∼ WRW^k_s(a, b)} [U_{⃗a}]`. -/
noncomputable def fk (k : ℕ) (a : A) (b : Inner m s) : Matrix (Fin D) (Fin D) ℝ :=
  fwdCond G u k (prodU U) a b

/-- The conditional mean `M_k(a) = E_b [f_k(a, b)]`. -/
noncomputable def Mka (k : ℕ) (a : A) : Matrix (Fin D) (Fin D) ℝ :=
  avg fun b : Inner m s => fk G u U k a b

/-- The mean `M_k = E_{a,b} [f_k(a, b)]`. -/
noncomputable def Mk (k : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  avg fun ab : A × Inner m s => fk G u U k ab.1 ab.2

/-- `τ_k² = ‖E_{a,b}[f_kᵀ f_k] - M_kᵀ M_k‖_op`. -/
noncomputable def tauSq (k : ℕ) : ℝ :=
  opNorm ((avg fun ab : A × Inner m s => (fk G u U k ab.1 ab.2)ᵀ * fk G u U k ab.1 ab.2)
    - (Mk G u U k)ᵀ * Mk G u U k)

/-- `μ_k² = ‖E_a [M_k(a)ᵀ M_k(a)]‖_op`. -/
noncomputable def muSq (k : ℕ) : ℝ :=
  opNorm (avg fun a : A => (Mka G u U k a)ᵀ * Mka G u U k a)

/-- `Φ_k = μ_k² + λ² τ_k²`. -/
noncomputable def Phi (lam : ℝ) (k : ℕ) : ℝ := muSq G u U k + lam ^ 2 * tauSq G u U k

/-- `g_{r,k}(a, b) = E_{⃗a ∼ ←WRW^r_s(a, b)} [U_{a_{r-1}} ⋯ U_{a₀} M_k(a₀)]`. -/
noncomputable def grk (r k : ℕ) (a : A) (b : Inner m s) : Matrix (Fin D) (Fin D) ℝ :=
  revCond G u r (fun w => revProdU U w * Mka G u U k (w 0)) a b

/-- `N_{r,k}(a) = E_b [g_{r,k}(a, b)]`. -/
noncomputable def Nrka (r k : ℕ) (a : A) : Matrix (Fin D) (Fin D) ℝ :=
  avg fun b : Inner m s => grk G u U r k a b

/-- `N_{r,k} = E_{a,b} [g_{r,k}(a, b)]`. -/
noncomputable def Nrk (r k : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  avg fun ab : A × Inner m s => grk G u U r k ab.1 ab.2

/-- `σ_{r,k}² = ‖E_{a,b}[g_{r,k}ᵀ g_{r,k}] - N_{r,k}ᵀ N_{r,k}‖_op`. -/
noncomputable def sigmaSq (r k : ℕ) : ℝ :=
  opNorm ((avg fun ab : A × Inner m s => (grk G u U r k ab.1 ab.2)ᵀ * grk G u U r k ab.1 ab.2)
    - (Nrk G u U r k)ᵀ * Nrk G u U r k)

/-- `Ψ_{r,k} = ‖N_{r,k}‖_op² + λ² σ_{r,k}²`. -/
noncomputable def Psi (lam : ℝ) (r k : ℕ) : ℝ :=
  opNorm (Nrk G u U r k) ^ 2 + lam ^ 2 * sigmaSq G u U r k

/-- The amplification threshold `H(s, t) = 2 (1/(9λ⁴))^{1 + t/s} (19λ²)^t`. -/
noncomputable def ampThreshold (lam : ℝ) (s t : ℕ) : ℝ :=
  2 * (1 / (9 * lam ^ 4)) ^ (1 + (t : ℝ) / s) * (19 * lam ^ 2) ^ t

end Amplification

/-- The reverse inner walk `b_k, b_{k-1}, …` (index `0` is `b_k`):
`b_{i-1} = shift⁻¹(b_i) + u_{j}` (a draw from `N ∘ shift⁻¹ (b_i)`). -/
def rbseq {m s q k : ℕ} (u : Fin q → Inner m s) (b : Inner m s) (js : Fin k → Fin q) : ℕ → Inner m s
  | 0 => b
  | i + 1 => shiftInv (rbseq u b js i) + genAt u js i

end ExpanderWalkDecode.Main


