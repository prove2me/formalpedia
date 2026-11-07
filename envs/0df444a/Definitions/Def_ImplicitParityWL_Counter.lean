-- Prove2me | Definitions.Def_ImplicitParityWL_Counter
-- name    : ImplicitParityWL_Counter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:18.564866+00:00
-- url     : https://prove2.me/theorems/aa027925-c4b1-42c8-b745-ccaa1a2e21a5
-- title:
--   The counter $\mathcal I^{k,\ell}_{\mathrm{ctr}}$
-- statement:
--   Fix $k$ and $\ell$ and put $m=(k-1)\ell$. The first $k-1$ blocks of an address hold $m$ data bits, read row by row with $(a_1)_1$ as least significant bit, and the last block is their checksum. The counter has
--
--   1. a main location $v$ with coordinate domain $\mathfrak c$;
--   2. for $0\le j<m$, private locations $p_j,q_j$ with coordinate domain $\mathfrak c'_j$, the coordinates whose bits are $1^j0x$;
--   3. endpoint locations $z_0,z_1$ with coordinate domains $\mathrm{supp}(s)$, $\mathrm{supp}(t)$, where $s$ has data bits $0\cdots0$ and $t$ has data bits $1\cdots1$.
--
--   Its $3m+2$ binary schemas give $X_{v,a}=X_{p_j,a}=X_{q_j,a}=X_{v,T_ja}$ for $a$ supported in $\mathfrak c'_j$, where the increment $T_j$ flips the leading $1$s to $0$, changes the first $0$ to $1$ and updates the checksum, together with $X_{z_0,s}=X_{v,s}$ and $X_{z_1,t}=X_{v,t}$. The initialization is $\iota(z_0)=0$, $\iota(z_1)=1$ and $\star$ elsewhere.
--
--   The system expands to an equality path through all $2^m$ counter values, and the mission applies the graph compiler to it.
--
--   **Formalization Note** The page's sentence defining $\mathfrak c'_j$ is informal about the checksum block. It is formalized as the union of $\mathrm{supp}(a)$ over the addresses whose data word has prefix $1^j0$. $T_j$ translates a data block by the indicator of the positions $\le j$ in its column and the last block by the sum of these translations. A script replayed these definitions for $(k,\ell)\in\{(3,1),(3,2),(3,3),(4,1),(4,2),(5,1),(5,2)\}$: the allowed addresses of $\mathfrak c'_j$ are exactly those with the prefix, and $T_j$ adds one to the data word.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §4.5, pp.22–23

import Mathlib
import Definitions.Def_ImplicitParityWL_ImplicitSystem

namespace ImplicitParityWL

variable {k ℓ : ℕ}

/-- The position `r (k - 1) + i` of the bit `(a_i)_r` in the data word, for a data block `i < k - 1`
(Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit
Parity Systems*, manuscript of November 3, 2026, §4.5, p.22, array (10)): the first `k - 1` columns
are read row by row, left to right and top to bottom, and position `0` is `(a₁)₁`, the least
significant bit. -/
def dataPos (k : ℕ) (i : Fin k) (r : Fin ℓ) : ℕ := r.val * (k - 1) + i.val

/-- Completes data blocks with their checksum: `withChecksum g i = g i` for `i < k - 1`, and the last
block is the sum of the data blocks (array (10), p.22). -/
def withChecksum {M : Type*} [AddCommMonoid M] (g : Fin k → M) : Fin k → M := fun i =>
  if i.val + 1 < k then g i else ∑ i' : Fin k, if i'.val + 1 < k then g i' else 0

theorem sum_withChecksum (g : Fin k → BlockCoord ℓ) : ∑ i, withChecksum g i = 0 := by
  cases k with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have hlast : withChecksum g (Fin.last n) =
        ∑ i : Fin n, g i.castSucc := by
      simp [withChecksum, Fin.sum_univ_castSucc]
    have hcast : ∀ i : Fin n, withChecksum g i.castSucc = g i.castSucc := by
      intro i
      simp [withChecksum]
    rw [hlast, Finset.sum_congr rfl (fun i _ => hcast i)]
    funext r
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- The address `s` with data bits `00⋯0` (§4.5, p.22): all block coordinates are `0^ℓ`. -/
def counterStart (k ℓ : ℕ) : Address k ℓ := ⟨fun _ _ => 0, by
  funext r; simp⟩

/-- The address `t` with data bits `11⋯1` and its checksum `(k - 1) 1^ℓ` (§4.5, p.22). -/
def counterEnd (k ℓ : ℕ) : Address k ℓ :=
  ⟨withChecksum (fun _ _ => 1), sum_withChecksum _⟩

/-- The address `a` has data word with prefix `1^j 0`: the data positions below `j` hold `1` and the
data position `j` holds `0`. -/
def HasPrefix (a : Address k ℓ) (j : ℕ) : Prop :=
  ∀ (i : Fin k) (r : Fin ℓ), i.val + 1 < k →
    (dataPos k i r < j → a.1 i r = 1) ∧ (dataPos k i r = j → a.1 i r = 0)

open scoped Classical in
/-- The coordinate domain `𝔠′_j` (§4.5, p.22): the coordinates whose bits are `1^j 0 x`, read across
all blocks.

**Formalization Note** The page's sentence is informal about the checksum block. It is formalized as
the union of `supp(a)` over the addresses `a` whose data word has prefix `1^j 0`, the product set the
sentence describes. -/
noncomputable def prefixDom (k ℓ : ℕ) (j : ℕ) : Finset (Coord k ℓ) :=
  Finset.univ.filter (fun c => ∃ a : Address k ℓ, HasPrefix a j ∧ c ∈ a.supp)

/-- The increment `T_j` (§4.5, p.23): it flips the data positions `≤ j` and updates the checksum
accordingly, by translating block `i < k - 1` by the indicator of those positions in column `i` and the
last block by the sum of these translations. On an address with prefix `1^j 0` it flips the leading
`1`s to `0` and the first `0` to `1`. -/
def stepPerm (k ℓ : ℕ) (j : ℕ) : BlockPerm k ℓ where
  f := 1
  δ := withChecksum (fun i r => if dataPos k i r ≤ j then 1 else 0)
  sum_δ := sum_withChecksum _

/-- The locations of the counter (§4.5, pp.22–23): the main location `v`, the private locations `p_j`,
`q_j` for `0 ≤ j < m`, and the endpoint locations `z₀`, `z₁`. -/
inductive CounterLoc (m : ℕ) where
  | main
  | p (j : Fin m)
  | q (j : Fin m)
  | z0
  | z1
  deriving DecidableEq, Fintype

/-- The `3m + 2` schemas of the counter (§4.5, p.23): for each `j` the chain `v, p_j, q_j, v`, and the
two endpoint schemas. -/
inductive CounterSchema (m : ℕ) where
  | vp (j : Fin m)
  | pq (j : Fin m)
  | qv (j : Fin m)
  | start
  | stop
  deriving DecidableEq, Fintype

/-- The schema of the counter with the given index (§4.5, p.23): `X_{v,a} = X_{p_j,a} = X_{q_j,a} =
X_{v,T_j a}` for `a` supported in `𝔠′_j`, `X_{z₀,s} = X_{v,s}` and `X_{z₁,t} = X_{v,t}`. All permutations are
identities except `T_j` at `v` in the last schema of each chain. -/
noncomputable def counterSchema (k ℓ : ℕ) :
    CounterSchema ((k - 1) * ℓ) → EquationSchema k ℓ (CounterLoc ((k - 1) * ℓ))
  | .vp j => ⟨.main, .p j, prefixDom k ℓ j, BlockPerm.id, BlockPerm.id, none⟩
  | .pq j => ⟨.p j, .q j, prefixDom k ℓ j, BlockPerm.id, BlockPerm.id, none⟩
  | .qv j => ⟨.q j, .main, prefixDom k ℓ j, BlockPerm.id, stepPerm k ℓ j, none⟩
  | .start => ⟨.z0, .main, (counterStart k ℓ).supp, BlockPerm.id, BlockPerm.id, none⟩
  | .stop => ⟨.z1, .main, (counterEnd k ℓ).supp, BlockPerm.id, BlockPerm.id, none⟩

/-- The coordinate domains of the counter (§4.5, pp.22–23): `𝔠` at `v`, `𝔠′_j` at `p_j` and `q_j`,
`supp(s)` at `z₀` and `supp(t)` at `z₁`. -/
noncomputable def counterDom (k ℓ : ℕ) :
    CounterLoc ((k - 1) * ℓ) → Finset (Coord k ℓ)
  | .main => Finset.univ
  | .p j => prefixDom k ℓ j
  | .q j => prefixDom k ℓ j
  | .z0 => (counterStart k ℓ).supp
  | .z1 => (counterEnd k ℓ).supp

theorem blockPerm_id_apply (c : Coord k ℓ) : (BlockPerm.id : BlockPerm k ℓ) c = c := by
  show ((1 : Equiv.Perm (Fin k)) c.1, c.2 + 0) = c
  simp

/-- The implicit parity system `ℐ_ctr^{k,ℓ}` (§4.5, pp.22–23), with `m = (k - 1)ℓ`. Its initialization is
`ι(z₀) = 0`, `ι(z₁) = 1` and `⋆` elsewhere. -/
noncomputable def counter (k ℓ : ℕ) :
    ImplicitSystem k ℓ (CounterLoc ((k - 1) * ℓ)) (CounterSchema ((k - 1) * ℓ)) where
  dom := counterDom k ℓ
  schema := counterSchema k ℓ
  wf := by
    intro e
    cases e <;>
      constructor <;> simp [counterSchema, counterDom, blockPerm_id_apply]
  share := by
    intro e f hef x hx y hy
    cases e <;> cases f <;>
      simp_all [counterSchema, EquationSchema.locs] <;>
      (try (rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩)) <;>
      (try (rcases hx1 with rfl | rfl <;> rcases hy1 with rfl | rfl <;> simp_all))
  init := fun
    | .z0 => some 0
    | .z1 => some 1
    | _ => none

end ImplicitParityWL


