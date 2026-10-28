-- Prove2me | Definitions.Def_BitcoinSer
-- name    : BitcoinSer
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T13:54:25.877193+00:00
-- url     : https://prove2.me/theorems/0ed76bcd-c76b-4e6f-a99b-ad36959f8841
-- title:
--   Serialization (CompactSize, transactions, headers, blocks), SHA-256d, Hash160, weights, and the genesis block
-- statement:
--   **Integers.** $\mathrm{leBytes}(k, n)$ is the $k$-byte little-endian encoding of $n$ modulo $2^{8k}$; $\mathrm{leVal}$ reads a byte list little-endian; $\mathrm{readLE}(k)$ consumes $k$ bytes (`none` if fewer remain). `ser8/16/32/64` are the fixed-width writers; signed 64/32-bit values are written two's-complement and read back with the sign restored. $\mathrm{MAX\_SIZE} = 2^{25}$.
--
--   **CompactSize.** $\mathrm{writeCompactSize}$ is `WriteCompactSize`: one byte below $253$, else a marker $253/254/255$ followed by $2/4/8$ little-endian bytes. $\mathrm{readCompactSize}(\text{rangeCheck})$ is `ReadCompactSize`: `none` on a short read, on a non-canonical encoding (a $2$-byte value below $253$, a $4$-byte value below $2^{16}$, an $8$-byte value below $2^{32}$), or, when range-checked, on a value above $\mathrm{MAX\_SIZE}$.
--
--   **Vectors and byte strings.** A vector is its CompactSize length followed by its elements; a byte string (`CScript`, witness element) is its length then its bytes; `uint256` is 32 raw bytes. Readers use the range-checked CompactSize, as the source's vector reader does.
--
--   **Transactions.** `OutPoint` (32-byte hash, `n`), `TxIn` (prevout, scriptSig, nSequence, witness stack), `TxOut` (`nValue : Int`, scriptPubKey), `Tx` (`version`, `vin`, `vout`, `nLockTime`). $\mathrm{serTx}(\text{allowWitness})$ is `SerializeTransaction`: the basic format `version vin vout nLockTime`, or, when witnesses are allowed and present (`hasWitness`), the BIP144 extended format with the dummy empty `vin` and flag byte $1$ before the real `vin`, and one witness stack per input before `nLockTime`. $\mathrm{readTx}(\text{allowWitness})$ is `UnserializeTransaction` with its exact control flow: an empty `vin` with witnesses allowed is reinterpreted as the dummy, a flag byte is read, flag bit $1$ reads the witnesses and rejects an all-empty witness record, any remaining flag bit rejects. $\mathrm{stripWitness}$ clears every witness stack.
--
--   **Headers and blocks.** `Header` is the 80-byte `CBlockHeader` (`int32 nVersion`, two 32-byte hashes, `nTime`, `nBits`, `nNonce`); `Block` is a header and a transaction vector; `serBlock`/`readBlock` take the same witness flag. The `wf` predicates state the field ranges under which serialization is faithful: 32-bit fields below $2^{32}$, hashes of 32 bytes, amounts in $[-2^{63}, 2^{63})$, lengths at most $\mathrm{MAX\_SIZE}$, and for a block every transaction has an input or a witness.
--
--   **Hashes.** $\mathrm{sha256}$, $\mathrm{ripemd160}$ and $\mathrm{sha1}$ are the full compression-function algorithms of `crypto/` (Merkle–Damgård padding, 64-byte chunks, 32-bit word arithmetic); $\mathrm{hash256} = \mathrm{sha256} \circ \mathrm{sha256}$ is `Hash`, $\mathrm{hash160} = \mathrm{ripemd160} \circ \mathrm{sha256}$ is `Hash160`; `txid` is `hash256` of the witness-stripped serialization, `wtxid` of the full one (equal to `txid` without witness), `headerHash` is `CBlockHeader::GetHash`.
--
--   **Weights and genesis.** `txWeight`/`blockWeight` are `GetTransactionWeight`/`GetBlockWeight` ($3 \cdot |\text{stripped}| + |\text{full}|$); `MAX_BLOCK_WEIGHT` $= 4{,}000{,}000$. `genesisCoinbase`, `genesisHeader`, `genesisBlock` transcribe `CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 COIN)` with the literal scriptSig and output script; `genesisHash` and `genesisMerkleRoot` are the hashes recorded in `chainparams.cpp` in serialized byte order.
--
--   **Formalization Note.** Byte lists and natural numbers replace streams and fixed-width C++ types; truncation modulo $2^{8k}$ models the writers on out-of-range values, which the `wf` predicates exclude. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Std

namespace BitcoinSer

/-! Transcription of Bitcoin Core's serialization and hashing at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `serialize.h` (little-endian integers,
`WriteCompactSize`/`ReadCompactSize`, vectors), `primitives/transaction.h`
(`SerializeTransaction`/`UnserializeTransaction`, BIP144 extended format), `primitives/block.h`
(`CBlockHeader`, `CBlock`), `hash.h` (SHA-256d, Hash160), `crypto/sha256.cpp`,
`crypto/ripemd160.cpp`, `crypto/sha1.cpp`, `consensus/validation.h` (weights), and the mainnet
genesis block of `kernel/chainparams.cpp`. Readers return `none` where the source throws. -/

abbrev Byte := BitVec 8
abbrev Bytes := List Byte

/-- `serialize.h`: `MAX_SIZE = 0x02000000`, the bound `ReadCompactSize` enforces by default. -/
def MAX_SIZE : Nat := 0x02000000

/-! ### Little-endian fixed-width integers -/

/-- `k` little-endian bytes of `n` (truncated modulo `2^(8k)`). -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 8 (n % 256) :: leBytes k (n / 256)

/-- The little-endian value of a byte list. -/
def leVal : Bytes → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * leVal rest

/-- Read `k` bytes as a little-endian number. -/
def readLE (k : Nat) (s : Bytes) : Option (Nat × Bytes) :=
  if s.length < k then none else some (leVal (s.take k), s.drop k)

/-- `k` big-endian bytes of `n`. -/
def beBytes (k n : Nat) : Bytes := (leBytes k n).reverse

/-- `ser_writedata8/16/32/64`. -/
def ser8 (n : Nat) : Bytes := leBytes 1 n
def ser16 (n : Nat) : Bytes := leBytes 2 n
def ser32 (n : Nat) : Bytes := leBytes 4 n
def ser64 (n : Nat) : Bytes := leBytes 8 n

/-- Signed 64-bit (`CAmount`) as two's complement little-endian. -/
def serInt64 (n : Int) : Bytes := leBytes 8 (n % 2 ^ 64).toNat
/-- Signed 32-bit (`int32_t nVersion`). -/
def serInt32 (n : Int) : Bytes := leBytes 4 (n % 2 ^ 32).toNat

def readInt64 (s : Bytes) : Option (Int × Bytes) :=
  (readLE 8 s).map fun (v, r) => (if v < 2 ^ 63 then (v : Int) else (v : Int) - 2 ^ 64, r)
def readInt32 (s : Bytes) : Option (Int × Bytes) :=
  (readLE 4 s).map fun (v, r) => (if v < 2 ^ 31 then (v : Int) else (v : Int) - 2 ^ 32, r)

/-! ### CompactSize -/

/-- `WriteCompactSize`. -/
def writeCompactSize (n : Nat) : Bytes :=
  if n < 253 then ser8 n
  else if n ≤ 0xffff then ser8 253 ++ ser16 n
  else if n ≤ 0xffffffff then ser8 254 ++ ser32 n
  else ser8 255 ++ ser64 n

/-- `ReadCompactSize(is, range_check)`: `none` on a short read, a non-canonical encoding, or
(with `rangeCheck`) a value above `MAX_SIZE`. -/
def readCompactSize (rangeCheck : Bool) (s : Bytes) : Option (Nat × Bytes) :=
  match s with
  | [] => none
  | ch :: rest =>
    let r : Option (Nat × Bytes) :=
      if ch.toNat < 253 then some (ch.toNat, rest)
      else if ch.toNat = 253 then
        match readLE 2 rest with
        | some (v, r) => if v < 253 then none else some (v, r)
        | none => none
      else if ch.toNat = 254 then
        match readLE 4 rest with
        | some (v, r) => if v < 0x10000 then none else some (v, r)
        | none => none
      else
        match readLE 8 rest with
        | some (v, r) => if v < 0x100000000 then none else some (v, r)
        | none => none
    match r with
    | some (v, r) => if rangeCheck && decide (MAX_SIZE < v) then none else some (v, r)
    | none => none

/-! ### Vectors and byte strings -/

/-- `Serialize(vector<T>)`: `WriteCompactSize(size)` then the elements. -/
def serList {α : Type} (f : α → Bytes) (l : List α) : Bytes :=
  writeCompactSize l.length ++ l.flatMap f

/-- Read exactly `n` elements with `f`. -/
def readN {α : Type} (f : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, s => some ([], s)
  | n + 1, s =>
    match f s with
    | none => none
    | some (x, s') =>
      match readN f n s' with
      | none => none
      | some (xs, s'') => some (x :: xs, s'')

/-- `Unserialize(vector<T>)`: a range-checked `ReadCompactSize`, then that many elements. -/
def readList {α : Type} (f : Bytes → Option (α × Bytes)) (s : Bytes) : Option (List α × Bytes) :=
  match readCompactSize true s with
  | none => none
  | some (n, s') => readN f n s'

/-- A byte vector (`CScript`, a witness stack element, `prevector`): length then raw bytes. -/
def serBytes (b : Bytes) : Bytes := writeCompactSize b.length ++ b

def readBytes (s : Bytes) : Option (Bytes × Bytes) :=
  match readCompactSize true s with
  | none => none
  | some (n, s') => if s'.length < n then none else some (s'.take n, s'.drop n)

/-- `uint256`: 32 raw bytes. -/
def readHash (s : Bytes) : Option (Bytes × Bytes) :=
  if s.length < 32 then none else some (s.take 32, s.drop 32)

/-! ### Transactions (`primitives/transaction.h`) -/

/-- `COutPoint { uint256 hash; uint32_t n; }`. -/
structure OutPoint where
  hash : Bytes
  n : Nat
  deriving DecidableEq, Repr

/-- `CTxIn`; `witness` is `scriptWitness.stack`, serialized only through the transaction. -/
structure TxIn where
  prevout : OutPoint
  scriptSig : Bytes
  nSequence : Nat
  witness : List Bytes
  deriving DecidableEq, Repr

/-- `CTxOut { CAmount nValue; CScript scriptPubKey; }`. -/
structure TxOut where
  nValue : Int
  scriptPubKey : Bytes
  deriving DecidableEq, Repr

/-- `CTransaction` data: `uint32_t version`, `vin`, `vout`, `uint32_t nLockTime`. -/
structure Tx where
  version : Nat
  vin : List TxIn
  vout : List TxOut
  nLockTime : Nat
  deriving DecidableEq, Repr

/-- `CTransaction::HasWitness`: some input has a non-empty witness stack. -/
def Tx.hasWitness (tx : Tx) : Bool := tx.vin.any fun i => !i.witness.isEmpty

/-- The transaction with every witness stack cleared (what `TX_NO_WITNESS` reading yields). -/
def Tx.stripWitness (tx : Tx) : Tx :=
  { tx with vin := tx.vin.map fun i => { i with witness := [] } }

def serOutPoint (o : OutPoint) : Bytes := o.hash ++ ser32 o.n
def serTxIn (i : TxIn) : Bytes := serOutPoint i.prevout ++ serBytes i.scriptSig ++ ser32 i.nSequence
def serTxOut (o : TxOut) : Bytes := serInt64 o.nValue ++ serBytes o.scriptPubKey

/-- `SerializeTransaction(tx, s, params)` with `params.allow_witness = allowWitness`. -/
def serTx (allowWitness : Bool) (tx : Tx) : Bytes :=
  let flags : Nat := if allowWitness && tx.hasWitness then 1 else 0
  ser32 tx.version ++
  (if flags ≠ 0 then writeCompactSize 0 ++ ser8 flags else []) ++
  serList serTxIn tx.vin ++ serList serTxOut tx.vout ++
  (if flags ≠ 0 then tx.vin.flatMap (fun i => serList serBytes i.witness) else []) ++
  ser32 tx.nLockTime

def readOutPoint (s : Bytes) : Option (OutPoint × Bytes) :=
  match readHash s with
  | none => none
  | some (h, s) =>
    match readLE 4 s with
    | none => none
    | some (n, s) => some (⟨h, n⟩, s)

def readTxIn (s : Bytes) : Option (TxIn × Bytes) :=
  match readOutPoint s with
  | none => none
  | some (p, s) =>
    match readBytes s with
    | none => none
    | some (sig, s) =>
      match readLE 4 s with
      | none => none
      | some (q, s) => some (⟨p, sig, q, []⟩, s)

def readTxOut (s : Bytes) : Option (TxOut × Bytes) :=
  match readInt64 s with
  | none => none
  | some (v, s) =>
    match readBytes s with
    | none => none
    | some (spk, s) => some (⟨v, spk⟩, s)

/-- Attach witness stacks to inputs, in order. -/
def attachWitness : List TxIn → List (List Bytes) → List TxIn
  | i :: is, w :: ws => { i with witness := w } :: attachWitness is ws
  | is, _ => is

/-- Read one witness stack per input. -/
def readWitnesses : Nat → Bytes → Option (List (List Bytes) × Bytes) :=
  readN (readList readBytes)

/-- `UnserializeTransaction(tx, s, params)` with `params.allow_witness = allowWitness`. -/
def readTx (allowWitness : Bool) (s : Bytes) : Option (Tx × Bytes) :=
  match readLE 4 s with
  | none => none
  | some (version, s) =>
    match readList readTxIn s with
    | none => none
    | some (vin0, s) =>
      -- `if (tx.vin.size() == 0 && fAllowWitness)`: read the flags byte and, if non-zero, vin/vout
      let step2 : Option (Nat × List TxIn × List TxOut × Bytes) :=
        if vin0.isEmpty && allowWitness then
          match s with
          | [] => none
          | fl :: s =>
            if fl.toNat ≠ 0 then
              match readList readTxIn s with
              | none => none
              | some (vin, s) =>
                match readList readTxOut s with
                | none => none
                | some (vout, s) => some (fl.toNat, vin, vout, s)
            else some (0, vin0, [], s)
        else
          match readList readTxOut s with
          | none => none
          | some (vout, s) => some (0, vin0, vout, s)
      match step2 with
      | none => none
      | some (flags, vin, vout, s) =>
        let step3 : Option (Nat × List TxIn × Bytes) :=
          if flags % 2 = 1 && allowWitness then
            match readWitnesses vin.length s with
            | none => none
            | some (ws, s) =>
              let vin' := attachWitness vin ws
              -- "Superfluous witness record"
              if (Tx.hasWitness ⟨0, vin', [], 0⟩) then some (flags - 1, vin', s) else none
          else some (flags, vin, s)
        match step3 with
        | none => none
        | some (flags, vin, s) =>
          -- "Unknown transaction optional data"
          if flags ≠ 0 then none
          else
            match readLE 4 s with
            | none => none
            | some (lock, s) => some (⟨version, vin, vout, lock⟩, s)

/-! ### Headers and blocks (`primitives/block.h`) -/

/-- `CBlockHeader`: `int32_t nVersion`, `uint256 hashPrevBlock`, `uint256 hashMerkleRoot`,
`uint32_t nTime`, `uint32_t nBits`, `uint32_t nNonce`. -/
structure Header where
  version : Int
  prevBlock : Bytes
  merkleRoot : Bytes
  time : Nat
  bits : Nat
  nonce : Nat
  deriving DecidableEq, Repr

def serHeader (h : Header) : Bytes :=
  serInt32 h.version ++ h.prevBlock ++ h.merkleRoot ++ ser32 h.time ++ ser32 h.bits ++ ser32 h.nonce

def readHeader (s : Bytes) : Option (Header × Bytes) :=
  match readInt32 s with
  | none => none
  | some (v, s) =>
    match readHash s with
    | none => none
    | some (p, s) =>
      match readHash s with
      | none => none
      | some (m, s) =>
        match readLE 4 s with
        | none => none
        | some (t, s) =>
          match readLE 4 s with
          | none => none
          | some (b, s) =>
            match readLE 4 s with
            | none => none
            | some (n, s) => some (⟨v, p, m, t, b, n⟩, s)

/-- `CBlock`: the header followed by `vtx`. -/
structure Block where
  header : Header
  vtx : List Tx
  deriving DecidableEq, Repr

def serBlock (allowWitness : Bool) (b : Block) : Bytes :=
  serHeader b.header ++ serList (serTx allowWitness) b.vtx

def readBlock (allowWitness : Bool) (s : Bytes) : Option (Block × Bytes) :=
  match readHeader s with
  | none => none
  | some (h, s) =>
    match readList (readTx allowWitness) s with
    | none => none
    | some (vtx, s) => some (⟨h, vtx⟩, s)

/-! ### Well-formedness: the field ranges under which serialization is faithful -/

def OutPoint.wf (o : OutPoint) : Prop := o.hash.length = 32 ∧ o.n < 2 ^ 32
def TxIn.wf (i : TxIn) : Prop :=
  i.prevout.wf ∧ i.scriptSig.length ≤ MAX_SIZE ∧ i.nSequence < 2 ^ 32 ∧
  i.witness.length ≤ MAX_SIZE ∧ ∀ w ∈ i.witness, w.length ≤ MAX_SIZE
def TxOut.wf (o : TxOut) : Prop :=
  -(2 ^ 63) ≤ o.nValue ∧ o.nValue < 2 ^ 63 ∧ o.scriptPubKey.length ≤ MAX_SIZE
def Tx.wf (tx : Tx) : Prop :=
  tx.version < 2 ^ 32 ∧ tx.nLockTime < 2 ^ 32 ∧ tx.vin.length ≤ MAX_SIZE ∧ tx.vout.length ≤ MAX_SIZE ∧
  (∀ i ∈ tx.vin, i.wf) ∧ (∀ o ∈ tx.vout, o.wf)
def Header.wf (h : Header) : Prop :=
  -(2 ^ 31) ≤ h.version ∧ h.version < 2 ^ 31 ∧ h.prevBlock.length = 32 ∧ h.merkleRoot.length = 32 ∧
  h.time < 2 ^ 32 ∧ h.bits < 2 ^ 32 ∧ h.nonce < 2 ^ 32
def Block.wf (b : Block) : Prop :=
  b.header.wf ∧ b.vtx.length ≤ MAX_SIZE ∧ ∀ tx ∈ b.vtx, tx.wf ∧ (tx.vin ≠ [] ∨ tx.hasWitness = true)

/-! ### SHA-256 (`crypto/sha256.cpp`, generic `Transform`) -/

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
def Ch (x y z : UInt32) : UInt32 := z ^^^ (x &&& (y ^^^ z))
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ||| (z &&& (x ||| y))
def Sigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def Sigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def sigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def sigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def sha256K : List UInt32 := [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221, 3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580, 3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

structure Sha256State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

def sha256Init : Sha256State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- One round: `t1 = h + Σ1(e) + Ch(e,f,g) + k + w`, `t2 = Σ0(a) + Maj(a,b,c)`. -/
def sha256Round (s : Sha256State) (kw : UInt32) : Sha256State :=
  let t1 := s.h + Sigma1 s.e + Ch s.e s.f s.g + kw
  let t2 := Sigma0 s.a + Maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Big-endian 32-bit words of a byte list (4 bytes each). -/
def be32Words : Bytes → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
    UInt32.ofNat (b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat) :: be32Words rest
  | _ => []

/-- Message schedule: `w[t] = σ1(w[t-2]) + w[t-7] + σ0(w[t-15]) + w[t-16]` for `16 ≤ t < 64`. -/
def sha256Schedule (w : List UInt32) : List UInt32 :=
  let rec go (w : List UInt32) : Nat → List UInt32
    | 0 => w
    | n + 1 =>
      let t := w.length
      let nw := sigma1 (w.getD (t - 2) 0) + w.getD (t - 7) 0 + sigma0 (w.getD (t - 15) 0) + w.getD (t - 16) 0
      go (w ++ [nw]) n
  go w 48

def sha256Compress (s : Sha256State) (chunk : Bytes) : Sha256State :=
  let w := sha256Schedule (be32Words chunk)
  let r := (sha256K.zipWith (· + ·) w).foldl sha256Round s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

/-- Split into 64-byte chunks (the input length is a multiple of 64); `fuel` bounds the recursion. -/
def chunks64Aux : Nat → Bytes → List Bytes
  | 0, _ => []
  | fuel + 1, s => if s.length < 64 then [] else s.take 64 :: chunks64Aux fuel (s.drop 64)

def chunks64 (s : Bytes) : List Bytes := chunks64Aux (s.length / 64) s

/-- MD padding: `0x80`, zeros to 56 mod 64, then the bit length as 8 bytes (big-endian for
SHA-256/SHA-1, little-endian for RIPEMD-160). -/
def mdPad (bigEndianLen : Bool) (msg : Bytes) : Bytes :=
  let zeros := (119 - msg.length % 64) % 64
  msg ++ [0x80] ++ List.replicate zeros 0 ++
    (if bigEndianLen then beBytes 8 (msg.length * 8) else leBytes 8 (msg.length * 8))

def be32Bytes (x : UInt32) : Bytes := beBytes 4 x.toNat
def le32Bytes (x : UInt32) : Bytes := leBytes 4 x.toNat

/-- `CSHA256().Write(msg).Finalize()`. -/
def sha256 (msg : Bytes) : Bytes :=
  let s := (chunks64 (mdPad true msg)).foldl sha256Compress sha256Init
  be32Bytes s.a ++ be32Bytes s.b ++ be32Bytes s.c ++ be32Bytes s.d ++
  be32Bytes s.e ++ be32Bytes s.f ++ be32Bytes s.g ++ be32Bytes s.h

/-! ### RIPEMD-160 (`crypto/ripemd160.cpp`) -/

def rol (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
def rf1 (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
def rf2 (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~x &&& z)
def rf3 (x y z : UInt32) : UInt32 := (x ||| ~~~y) ^^^ z
def rf4 (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~z)
def rf5 (x y z : UInt32) : UInt32 := x ^^^ (y ||| ~~~z)

/-- Little-endian 32-bit words of a byte list. -/
def le32Words : Bytes → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
    UInt32.ofNat (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24) :: le32Words rest
  | _ => []

/-- Message-word selection and rotation amounts of the left and right lines. -/
def ripemdRL : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
def ripemdRR : List Nat := [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
def ripemdSL : List Nat := [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
def ripemdSR : List Nat := [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

structure R5 where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

def ripemdInit : R5 := ⟨0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0⟩

/-- Left line: `f1..f5` with constants `0, 5A827999, 6ED9EBA1, 8F1BBCDC, A953FD4E`. -/
def ripemdFL (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then rf1 x y z else if j < 32 then rf2 x y z else if j < 48 then rf3 x y z
  else if j < 64 then rf4 x y z else rf5 x y z
def ripemdKL (j : Nat) : UInt32 :=
  if j < 16 then 0 else if j < 32 then 0x5A827999 else if j < 48 then 0x6ED9EBA1
  else if j < 64 then 0x8F1BBCDC else 0xA953FD4E
/-- Right line: `f5..f1` with constants `50A28BE6, 5C4DD124, 6D703EF3, 7A6D76E9, 0`. -/
def ripemdFR (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then rf5 x y z else if j < 32 then rf4 x y z else if j < 48 then rf3 x y z
  else if j < 64 then rf2 x y z else rf1 x y z
def ripemdKR (j : Nat) : UInt32 :=
  if j < 16 then 0x50A28BE6 else if j < 32 then 0x5C4DD124 else if j < 48 then 0x6D703EF3
  else if j < 64 then 0x7A6D76E9 else 0

/-- `Round`: `a = rol(a + f + x + k, r) + e; c = rol(c, 10)`, then the register rotation. -/
def ripemdStep (s : R5) (f : UInt32) (x k : UInt32) (r : Nat) : R5 :=
  let a := rol (s.a + f + x + k) (UInt32.ofNat r) + s.e
  let c := rol s.c 10
  ⟨s.e, a, s.b, c, s.d⟩

def ripemdLine (w : List UInt32) (fsel : Nat → UInt32 → UInt32 → UInt32 → UInt32) (ksel : Nat → UInt32)
    (rsel ssel : List Nat) (s : R5) : R5 :=
  (List.range 80).foldl (fun s j =>
    ripemdStep s (fsel j s.b s.c s.d) (w.getD (rsel.getD j 0) 0) (ksel j) (ssel.getD j 0)) s

def ripemdCompress (s : R5) (chunk : Bytes) : R5 :=
  let w := le32Words chunk
  let l := ripemdLine w ripemdFL ripemdKL ripemdRL ripemdSL s
  let r := ripemdLine w ripemdFR ripemdKR ripemdRR ripemdSR s
  ⟨s.b + l.c + r.d, s.c + l.d + r.e, s.d + l.e + r.a, s.e + l.a + r.b, s.a + l.b + r.c⟩

/-- `CRIPEMD160().Write(msg).Finalize()`. -/
def ripemd160 (msg : Bytes) : Bytes :=
  let s := (chunks64 (mdPad false msg)).foldl ripemdCompress ripemdInit
  le32Bytes s.a ++ le32Bytes s.b ++ le32Bytes s.c ++ le32Bytes s.d ++ le32Bytes s.e

/-! ### SHA-1 (`crypto/sha1.cpp`) -/

def sha1F (t : Nat) (b c d : UInt32) : UInt32 :=
  if t < 20 then d ^^^ (b &&& (c ^^^ d)) else if t < 40 then b ^^^ c ^^^ d
  else if t < 60 then (b &&& c) ||| (d &&& (b ||| c)) else b ^^^ c ^^^ d
def sha1K (t : Nat) : UInt32 :=
  if t < 20 then 0x5A827999 else if t < 40 then 0x6ED9EBA1 else if t < 60 then 0x8F1BBCDC else 0xCA62C1D6

def sha1Schedule (w : List UInt32) : List UInt32 :=
  let rec go (w : List UInt32) : Nat → List UInt32
    | 0 => w
    | n + 1 =>
      let t := w.length
      let nw := rol (w.getD (t - 3) 0 ^^^ w.getD (t - 8) 0 ^^^ w.getD (t - 14) 0 ^^^ w.getD (t - 16) 0) 1
      go (w ++ [nw]) n
  go w 64

def sha1Compress (s : R5) (chunk : Bytes) : R5 :=
  let w := sha1Schedule (be32Words chunk)
  let r := (List.range 80).foldl (fun (s : R5) t =>
    let temp := rol s.a 5 + sha1F t s.b s.c s.d + s.e + sha1K t + w.getD t 0
    ⟨temp, s.a, rol s.b 30, s.c, s.d⟩) s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e⟩

def sha1 (msg : Bytes) : Bytes :=
  let s := (chunks64 (mdPad true msg)).foldl sha1Compress ripemdInit
  be32Bytes s.a ++ be32Bytes s.b ++ be32Bytes s.c ++ be32Bytes s.d ++ be32Bytes s.e

/-! ### Hashes of Bitcoin objects (`hash.h`, `primitives`) -/

/-- `Hash(x)` = SHA-256d. -/
def hash256 (m : Bytes) : Bytes := sha256 (sha256 m)
/-- `Hash160(x)` = RIPEMD-160 ∘ SHA-256. -/
def hash160 (m : Bytes) : Bytes := ripemd160 (sha256 m)

/-- `CTransaction::ComputeHash`: SHA-256d of the witness-stripped serialization. -/
def txid (tx : Tx) : Bytes := hash256 (serTx false tx)
/-- `CTransaction::ComputeWitnessHash`: equals `txid` when there is no witness. -/
def wtxid (tx : Tx) : Bytes := if tx.hasWitness then hash256 (serTx true tx) else txid tx
/-- `CBlockHeader::GetHash`. -/
def headerHash (h : Header) : Bytes := hash256 (serHeader h)

/-! ### Weights (`consensus/consensus.h`, `consensus/validation.h`) -/

def WITNESS_SCALE_FACTOR : Nat := 4
def MAX_BLOCK_WEIGHT : Nat := 4000000
def MAX_BLOCK_SERIALIZED_SIZE : Nat := 4000000

/-- `GetTransactionWeight`: `|TX_NO_WITNESS| * 3 + |TX_WITH_WITNESS|`. -/
def txWeight (tx : Tx) : Nat := (serTx false tx).length * (WITNESS_SCALE_FACTOR - 1) + (serTx true tx).length
/-- `GetBlockWeight`. -/
def blockWeight (b : Block) : Nat :=
  (serBlock false b).length * (WITNESS_SCALE_FACTOR - 1) + (serBlock true b).length

/-! ### The mainnet genesis block (`kernel/chainparams.cpp`, `CreateGenesisBlock`) -/

/-- `CScript() << 486604799 << CScriptNum(4) << "The Times 03/Jan/2009 Chancellor on brink of
second bailout for banks"`. -/
def genesisScriptSig : Bytes := [0x04, 0xff, 0xff, 0x00, 0x1d, 0x01, 0x04, 0x45, 0x54, 0x68, 0x65, 0x20, 0x54, 0x69, 0x6d, 0x65, 0x73, 0x20, 0x30, 0x33, 0x2f, 0x4a, 0x61, 0x6e, 0x2f, 0x32, 0x30, 0x30, 0x39, 0x20, 0x43, 0x68, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x6c, 0x6f, 0x72, 0x20, 0x6f, 0x6e, 0x20, 0x62, 0x72, 0x69, 0x6e, 0x6b, 0x20, 0x6f, 0x66, 0x20, 0x73, 0x65, 0x63, 0x6f, 0x6e, 0x64, 0x20, 0x62, 0x61, 0x69, 0x6c, 0x6f, 0x75, 0x74, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x62, 0x61, 0x6e, 0x6b, 0x73]

/-- `CScript() << 04678afd…11d5f << OP_CHECKSIG`. -/
def genesisOutputScript : Bytes := [0x41, 0x04, 0x67, 0x8a, 0xfd, 0xb0, 0xfe, 0x55, 0x48, 0x27, 0x19, 0x67, 0xf1, 0xa6, 0x71, 0x30, 0xb7, 0x10, 0x5c, 0xd6, 0xa8, 0x28, 0xe0, 0x39, 0x09, 0xa6, 0x79, 0x62, 0xe0, 0xea, 0x1f, 0x61, 0xde, 0xb6, 0x49, 0xf6, 0xbc, 0x3f, 0x4c, 0xef, 0x38, 0xc4, 0xf3, 0x55, 0x04, 0xe5, 0x1e, 0xc1, 0x12, 0xde, 0x5c, 0x38, 0x4d, 0xf7, 0xba, 0x0b, 0x8d, 0x57, 0x8a, 0x4c, 0x70, 0x2b, 0x6b, 0xf1, 0x1d, 0x5f, 0xac]

def genesisCoinbase : Tx :=
  ⟨1, [⟨⟨List.replicate 32 0, 0xffffffff⟩, genesisScriptSig, 0xffffffff, []⟩],
      [⟨5000000000, genesisOutputScript⟩], 0⟩

/-- `CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 * COIN)`; the merkle root of a
single-transaction block is that transaction's txid. -/
def genesisHeader : Header :=
  ⟨1, List.replicate 32 0, txid genesisCoinbase, 1231006505, 0x1d00ffff, 2083236893⟩

def genesisBlock : Block := ⟨genesisHeader, [genesisCoinbase]⟩

/-- `consensus.hashGenesisBlock = 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f`
(byte order as serialized, i.e. reversed display order). -/
def genesisHash : Bytes := [0x6f, 0xe2, 0x8c, 0x0a, 0xb6, 0xf1, 0xb3, 0x72, 0xc1, 0xa6, 0xa2, 0x46, 0xae, 0x63, 0xf7, 0x4f, 0x93, 0x1e, 0x83, 0x65, 0xe1, 0x5a, 0x08, 0x9c, 0x68, 0xd6, 0x19, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `genesis.hashMerkleRoot == 4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b`. -/
def genesisMerkleRoot : Bytes := [0x3b, 0xa3, 0xed, 0xfd, 0x7a, 0x7b, 0x12, 0xb2, 0x7a, 0xc7, 0x2c, 0x3e, 0x67, 0x76, 0x8f, 0x61, 0x7f, 0xc8, 0x1b, 0xc3, 0x88, 0x8a, 0x51, 0x32, 0x3a, 0x9f, 0xb8, 0xaa, 0x4b, 0x1e, 0x5e, 0x4a]

end BitcoinSer


